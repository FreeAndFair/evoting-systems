#!/usr/bin/env python
import sys
import os
import pdb
import shutil
import errno
import getopt
import logging
import gc
import site; site.addsitedir(os.path.expanduser("~/tevs")) 
import Image, ImageStat, ImageDraw 

import const #To be deprecated
import config
import util
import db
import next
import Ballot
BallotException = Ballot.BallotException

def get_args():
    """Get command line arguments"""
    try:
        opts, args = getopt.getopt(sys.argv[1:],
                                    "tdc:",
                                    ["templates",
                                     "debug",
                                     "config="
                                    ]
                                   ) 
    except getopt.GetoptError:
        #note that logging doesn't exist yet
        sys.stderr.write(
            "usage: %s -tdc --templates --debug --config=file" % sys.argv[0]
        )
        sys.exit(2)
    templates_only = False
    debug = False
    config = "tevs.cfg"
    for opt, arg in opts:
        if opt in ("-t", "--templates"):
            templates_only = True
        if opt in ("-d", "--debug"):
            debug = True
        if opt in ("-c", "--config"):
            config = arg

    const.templates_only = templates_only
    const.debug = debug
    return config

def remove_partial(fname):
    try:
        os.unlink(fname)
    except KeyboardInterrupt:
        raise
    except Exception: #bad form but we really don't care
        pass

def _fn(n):
    return "%03d" % (n/1000,)

def incomingn(n):
    return filen(os.path.join(const.incoming, _fn(n)), n) + const.filename_extension

def dirn(dir, n): # where dir is the "unrooted" name
    return util.root(dir, _fn(n))

def filen(dir, n): #where dir is from dirn
    return os.path.join(dir, "%06d" % n)

def mark_error(e, *files):
    log = logging.getLogger('')
    if e is not None:
        log.error(e)
    for file in files:
        log.error("Could not process ballot " + os.path.basename(file))
        try:
            shutil.copy2(file, util.root("errors", os.path.basename(file)))
        except IOError:
            log.error("Could not copy unprocessable file to errors dir")
    return len(files)

def results_to_vop_files(results,resultsfilename):
    """Save all ovals from a list of Votedata"""
    for r in results:
        label = "%s_%04d_%04d_%s_%s.jpg" % (
            resultsfilename,
            r.coords[0],
            r.coords[1],
            "V" if r.was_voted else "v",
            "A" if r.ambiguous else "a"
        )
        try:
            if r.image is not None:
                r.image.save(label)
        except Exception as e:
            print e

def main():
    miss_counter = 0
    # get command line arguments
    cfg_file = get_args()

    # read configuration from tevs.cfg and set constants for this run
    config.get(cfg_file)
    util.mkdirp(const.root)
    log = config.logger(const.logfilename)

    #create initial top level dirs, if they do not exist
    for p in (
        "%s" % ("templates"), 
        "%s%d" % ("template_images",  os.getpid()), 
        "%s%d" % ("composite_images", os.getpid()), 
        "results", 
        "proc",
        "errors"):
        util.mkdirp(util.root(p))

    next_ballot = next.File(util.root("nexttoprocess.txt"), const.num_pages)

    try:
        ballotfrom = Ballot.LoadBallotType(const.layout_brand)
    except KeyError as e:
        util.fatal("No such ballot type: " + const.layout_brand + ": check " + cfg_file)

    # allow all instances to share a common template location,
    # though need per-pid locs for template_images and composite_images
    cache = Ballot.TemplateCache(util.root("templates"))
    extensions = Ballot.Extensions(template_cache=cache)
   
    # connect to db and open cursor
    if const.use_db:
        try:
            dbc = db.PostgresDB(const.dbname, const.dbuser)
        except db.DatabaseError:
            util.fatal("Could not connect to database")
    else:
        dbc = db.NullDB()

    total_proc, total_unproc = 0, 0
    base = os.path.basename
    # While ballot images exist in the directory specified in tevs.cfg,
    # create ballot from images, get landmarks, get layout code, get votes.
    # Write votes to database and results directory.  Repeat.
    #from guppy import hpy;hp=hpy();hp.setref();import gc;gc.disable();gc.collect();hp.setref()
    try:
        for n in next_ballot:
            gc.collect()
            unprocs = [incomingn(n + m) for m in range(const.num_pages)]
            if not os.path.exists(unprocs[0]):
                miss_counter += 1
                log.info(base(unprocs[0]) + " does not exist. No more records to process")
                if miss_counter > 10:
                    break
                continue
            #for i, f in enumerate(unprocs[1:]):
            #    if not os.path.exists(f):
            #        log.info(base(f) + " does not exist. Cannot proceed.")
            #        for j in range(i):
            #            log.info(base(unprocs[j]) + " will NOT be processed")
            #        total_unproc += mark_error(None, *unprocs[:i-1])
                    

            #Processing

            log.info("Processing %s:\n %s" % 
                (n, "\n".join("\t%s" % base(u) for u in unprocs))
            )

            try:
                ballot = ballotfrom(unprocs, extensions)
                results = ballot.ProcessPages()
            except BallotException as e:
                total_unproc += mark_error(e, *unprocs)
                log.exception("Could not process ballot")
                continue

            csv = Ballot.results_to_CSV(results)
            #moz = Ballot.results_to_mosaic(results)
            
            #Write all data

            #make dirs:
            proc1d = dirn("proc", n)
            resultsd = dirn("results", n)
            resultsfilename = filen(resultsd, n)
            for p in (proc1d, resultsd):
                util.mkdirp(p)
            try:
                results_to_vop_files(results,resultsfilename)
            except Exception as e:
                print e
            #write csv and mosaic
            util.genwriteto(resultsfilename + ".txt", csv)
            #write to the database
            try:
                dbc.insert(ballot)
            except db.DatabaseError:
                #dbc does not commit if there is an error, just need to remove 
                #partial files
                remove_partial(resultsfilename + ".txt")
                remove_partial(resultsfilename + const.filename_extension)
                util.fatal("Could not commit vote information to database")

            #Post-processing

            # move the images from unproc to proc
            procs = [filen(proc1d, n + m) + const.filename_extension
                        for m in range(const.num_pages)]
            for a, b in zip(unprocs, procs):
                try:
                    os.rename(a, b)
                except OSError as e:
                    util.fatal("Could not rename %s", a)
            total_proc += const.num_pages
            log.info("%d images processed", const.num_pages)
            #hp.heap().dump('prof.hpy');hp.setref();gc.collect();hp.setref();hp.heap().dump('prof.hpy')
    finally:
        cache.save_all()
        dbc.close()
        next_ballot.save()
        log.info("%d images processed", total_proc)
        if total_unproc > 0:
            log.warning("%d images NOT processed.", total_unproc)

if __name__ == "__main__":
    main()
    #import cProfile as profile
    #profile.Profile.bias = 3.15e-6
    #profile.run('main()', 'prof.%s' % sys.argv[1])
