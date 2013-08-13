import os, sys, traceback, pdb, time, argparse, multiprocessing
try:
    import cPickle as pickle
except ImportError:
    import pickle
from os.path import join as pathjoin

import cv

from Vendor import Vendor

sys.path.append('..')

import barcode.hart as hart, asize
from grouping import partask

# Get this script's directory. Necessary to know this information
# since the current working directory may not be the same as where
# this script lives (which is important for loading resources like
# imgs)
try:
    MYDIR = os.path.abspath(os.path.dirname(__file__))
except NameError:
    # This script is being run directly
    MYDIR = os.path.abspath(sys.path[0])

TOP_GUARD_IMGP = pathjoin(MYDIR, 'hart_topguard.png')
BOT_GUARD_IMGP = pathjoin(MYDIR, 'hart_botguard.png')

TOP_GUARD_SKINNY_IMGP = pathjoin(MYDIR, 'hart_topguard_skinny.png')
BOT_GUARD_SKINNY_IMGP = pathjoin(MYDIR, 'hart_botguard_skinny.png')

class HartVendor(Vendor):
    def __init__(self, proj):
        self.proj = proj
    
    def decode_ballots(self, ballots, manager=None, queue=None, skipVerify=True, cache=None, *args, **kwargs):
        """
        Input:
            dict BALLOTS: {int ballotid: (str imgpath_0, ...)}
            dict CACHE: {str imgpath: (tuple decodings, bool isflipped)}
        Output:
            (dict IMG2DECODING,
             dict FLIPMAP,
             dict BBSTRIPES_MAP,
             list ERR_IMGPATHS,
             list IOERR_IMGPATHS)
        """
        topbot_paths = [[TOP_GUARD_IMGP, BOT_GUARD_IMGP], [TOP_GUARD_SKINNY_IMGP, BOT_GUARD_SKINNY_IMGP]]
        # DECODED_RESULTS_MAP: {ballotID: [(BCS, isflip, BBS, bbstripes_dict), ...]}
        decoded_results_map = decode_ballots(ballots, topbot_paths, manager, queue, skipVerify=skipVerify, cache=cache)
        flipmap = {} # maps {imgpath: bool isFlipped}
        bbstripes_map = {} # maps {'wideNarrow': [(str imgpath, (x1,y1,x2,y2), int id), ...], ...}
        err_imgpaths = []
        ioerr_imgpaths = []
        img2decoding = {}
        for ballotid, decoded_results in decoded_results_map.iteritems():
            imgpaths = ballots[ballotid]
            for i, subtuple in enumerate(decoded_results):
                if issubclass(type(subtuple), IOError):
                    ioerr_imgpaths.append(subtuple.filename)
                    continue
                bcs, isflipped, bbs, bbstripes_dict = subtuple
                imgpath = imgpaths[i]
                flipmap[imgpath] = isflipped
                bc_ul = bcs[0]
                if not bc_ul:
                    print "..error on: {0}".format(imgpath)
                    err_imgpaths.append(imgpath)
                elif skipVerify:
                    img2decoding[imgpath] = (bc_ul,)
                else:
                    img2decoding[imgpath] = (bc_ul,)
                    # First, maintain a global ordering of each stripe, for bbstripe_idx
                    stripe_y1s = []
                    for label, bbstripes in bbstripes_dict.iteritems():
                        for (x1,y1,x2,y2) in bbstripes:
                            stripe_y1s.append(y1)
                    # sort by Y1, bottom->top
                    stripe_y1s = sorted(stripe_y1s, key=lambda t: -t)
                    for label, bbstripes in bbstripes_dict.iteritems():
                        for (x1,y1,x2,y2) in bbstripes:
                            bbstripe_idx = stripe_y1s.index(y1)
                            bbstripes_map.setdefault(label, []).append((imgpath, (x1,y1,x2,y2), bbstripe_idx))
                            
        def sizeit(thing):
            nbytes = asize.asizeof(thing)
            return "{0} bytes ({1} MB)".format(nbytes, nbytes / 1e6)
        total_bytes = asize.asizeof(decoded_results_map) + asize.asizeof(flipmap) + asize.asizeof(bbstripes_map)
        print "decoded_results_map: {0} ({1:.4f}%)".format(sizeit(decoded_results_map), 100.0 * (asize.asizeof(decoded_results_map) / float(total_bytes)))
        print "flipmap: {0} ({1:.4f}%)".format(sizeit(flipmap), 100.0 * (asize.asizeof(flipmap) / float(total_bytes)))
        print "bbstripes_map: {0} ({1:.4f}%)".format(sizeit(bbstripes_map), 100.0 * (asize.asizeof(bbstripes_map) / float(total_bytes)))

        print "    Total: {0} bytes ({1} MB)".format(total_bytes, total_bytes / 1e6)
        total_bytes_oc = (666137 / (float(len(flipmap)))) * total_bytes
        print "    Total (Extrapolate to Full OC): {0} MB ({1} GB)".format(total_bytes_oc / 1e6, total_bytes_oc / 1e9)

        """ TODO: Crazy Memory usage here. At this point, for full OC estimate, we would
        use:
            Total (Extrapolate to Full OC): 18955.6165387 MB (18.9556165387 GB)
        The huge hitters are decoded_results_map (~9 GB) and bbstripes_map (~11 GB).
        """

        return img2decoding, flipmap, bbstripes_map, err_imgpaths, ioerr_imgpaths

    def partition_ballots(self, img2decoding, verified_results, manual_labeled):
        """
        Input:
            dict IMG2DECODING:
            dict VERIFIED_RESULTS:
                If this is None, then the user skipped overlay verification, so just
                use the input IMG2DECODING information.
            dict MANUAL_LABELED: {str imgpath: (str bc,)}
        Output:
            (dict PARTITIONS, dict IMG2DECODING, dict IMGINFO_MAP)
        """
        if verified_results == None:
            verified_results = {}
        if manual_labeled == None:
            manual_labeled = ()

        partitions = {} # maps {partitionID: [int ballotID, ...]}
        imginfo_map = {} # maps {imgpath: {str PROPNAME: str PROPVAL}}
        attrs2partitionID = {} # maps {('precinct', 'language', 'party'): int partitionID}
        bal2imgs = pickle.load(open(self.proj.ballot_to_images, 'rb'))
        img2bal = pickle.load(open(self.proj.image_to_ballot, 'rb'))
        if verified_results:
            img2decoding = {} # Ignore the input IMG2DECODING
            img_bc_temp = {} # maps {imgpath: [(i, bcLabel_i), ...]}
            for bc_val, tups in verified_results.iteritems():
                for (imgpath, (x1,y1,x2,y2), bbstripe_i) in tups:
                    img_bc_temp.setdefault(imgpath, []).append((bbstripe_i, bc_val))
            # IMG_DECODED_MAP: {str imgpath: str decoding}
            img_decoded_map = hart.interpret_labels(img_bc_temp)
            for imgpath, decoding in img_decoded_map.iteritems():
                img2decoding[imgpath] = (decoding,)
            del img_decoded_map

        # This keeps track of the info from the imginfo_map for each ballot,
        # to avoid decoding errors resulting in different images from the
        # same ballot being assigned to different partitions.
        bal2info = {} # maps {int ballotid: {str PROPNAME: str PROPVAL}}
        def add_decoding(imgpath, decoding):
            """ Registers the decoding for IMGPATH to a few data structures. """
            ballotid = img2bal[imgpath]
            imginfo = hart.get_info(decoding)
            
            imginfo_prev = bal2info.get(ballotid, None)
            if imginfo_prev == None:
                bal2info[ballotid] = imginfo
            else:
                # Ensure that the 'tag' portion is consistent within a ballot
                imginfo['precinct'] = imginfo_prev['precinct']
                imginfo['language'] = imginfo_prev['language']
                imginfo['party']    = imginfo_prev['party']
            imginfo_map[imgpath] = imginfo

        for imgpath, decoding in img2decoding.iteritems():
            # DECODING is a tuple of strings
            add_decoding(imgpath, decoding)
            
        for imgpath, decoding_tuple in manual_labeled.iteritems():
            add_decoding(imgpath, decoding_tuple[0])

        tag2partid = {} # maps {tag: int partitionid}
        curpartid = 0
        for balid, info in bal2info.iteritems():
            # The set of present pages is also a partitioning criterion.
            # In var-numpages elections, we don't want to clump together
            # a ballot with pages [1,2] and [2,3] together, for instance.
            pages = []
            flag_imageBad = False
            for imgpath in bal2imgs[balid]:
                if imgpath in imginfo_map:
                    pages.append(imginfo_map[imgpath]['page'])
                else:
                    # This image was either quarantined or discarded: 
                    # ignore this.
                    flag_imageOut = True
                    break
            if flag_imageBad:
                # At least one image in this ballot was quarantined/discarded,
                # so don't process the entire ballot.
                continue
                
            pages = tuple(sorted(pages))
            tag = info['precinct'], info['language'], info['party'], pages
            partid = tag2partid.get(tag, None)
            if partid == None:
                tag2partid[tag] = curpartid
                partid = curpartid
                curpartid += 1
            partitions.setdefault(partid, []).append(balid)

        for partitionid, ballotids in partitions.iteritems():
            partitions[partitionid] = sorted(set(ballotids))
        return partitions, img2decoding, imginfo_map

    def get_grouping_propnames(self):
        """ Hart ballots group by: Language, Party, Precinct. """
        return ('precinct', 'language', 'party') 

    def __repr__(self):
        return 'HartVendor()'
    def __str__(self):
        return 'HartVendor()'

def _do_decode_ballots(ballots, (topbot_paths, skipVerify, cache), queue=None):
    cvread = lambda imP: cv.LoadImage(imP, cv.CV_LOAD_IMAGE_GRAYSCALE)
    topbot_pairs = [[cvread(topbot_paths[0][0]), cvread(topbot_paths[0][1])],
                    [cvread(topbot_paths[1][0]), cvread(topbot_paths[1][1])]]
    results = {} # maps {int ballotid: [(bcs_side0, isflipped_side0, bbs_side0, bbstripes_side0), ...]}
    for ballotid, imgpaths in ballots.iteritems():
        balresults = []
        for imgpath in imgpaths:
            if cache and imgpath in cache:
                bcs, isflipped = cache[imgpath]
                balresults.append((bcs, isflipped, None, None))
                continue
            try:
                bcs, isflipped, bbs, bbstripes_dict = hart.decode(imgpath, topbot_pairs, skipVerify=skipVerify)
                balresults.append((bcs, isflipped, bbs, bbstripes_dict))
            except IOError as e:
                balresults.append(e)
        results[ballotid] = balresults
        if queue:
            queue.put(True)
    return results

def decode_ballots(ballots, topbot_paths, manager, queue, skipVerify=True, N=None, cache=None):
    t = time.time()
    decoded_results = partask.do_partask(_do_decode_ballots,
                                         ballots,
                                         _args=(topbot_paths, skipVerify, cache),
                                         combfn='dict',
                                         manager=manager,
                                         pass_queue=queue,
                                         N=N)
    dur = time.time() - t
    print "...finished decoding {0} ballots ({1:.2f}s, {2:.5f} secs per ballot)".format(len(ballots), dur, dur / float(len(ballots)))
    return decoded_results

def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("projdir")
    parser.add_argument("--n", type=int,
                        help="Process only the first N ballots in the election.")
    parser.add_argument("--fromfile", metavar="FILE",
                        help="Run decoding on a subset of the ballots from the \
election. Either a pickle'd python list/tuple of ballotids, or a textfile with \
ballotids on every line.")

    parser.add_argument("--numprocs", type=int,
                        help="Number of processes to use when decoding.")

    return parser.parse_args()

def main():
    args = parse_args()

    projdir = args.projdir

    if args.fromfile:
        filepath = args.fromfile
        if filepath.endswith(".p"):
            balids = pickle.load(open(filepath, 'rb'))
            if args.n != None:
                balids = balids[:args.n]
        else:
            f = open(filepath, 'r')
            balids = []
            for line in f.readlines():
                if args.n != None and len(balids) >= args.n:
                    break
                if not line: continue
                line = line.strip()
                if not line or line.startswith("#"): continue
                try:
                    balids.append(int(line))
                except:
                    print "(Main) Error trying to read ballotid:", line
            f.close()
    else:
        balids = None

    bal2imgs = pickle.load(open(pathjoin(projdir, 'ballot_to_images.p')))
    if not balids:
        balids = []
        if args.n != None:
            balids = list(sorted(bal2imgs.keys())[:args.n])
        else:
            balids = tuple(sorted(bal2imgs.keys()))

    cnt_imgs = 0
    bal2imgs_in = {} # maps {int ballotid: (str imgpath0, ...)}
    for balid in balids:
        imgpaths = bal2imgs[balid]
        bal2imgs_in[balid] = imgpaths
        cnt_imgs += len(imgpaths)

    print "(Info) Decoding {0} ballots ({1} images)".format(len(balids), cnt_imgs)

    topbot_paths = [[TOP_GUARD_IMGP, BOT_GUARD_IMGP], [TOP_GUARD_SKINNY_IMGP, BOT_GUARD_SKINNY_IMGP]]    
    manager = multiprocessing.Manager()
    queue = manager.Queue()

    # DECODED_RESULTS: {ballotID: [(BCS, isflip, BBS, bbstripes_dict), ...]}
    decoded_results = decode_ballots(bal2imgs_in, topbot_paths, manager, queue, skipVerify=True, N=args.numprocs)

    img2dec = {}
    img2flip = {}
    err_imgpaths, ioerr_imgpaths = [], []
    
    for i, (balid, infotuples) in enumerate(sorted(decoded_results.iteritems())):
        print "({0}) ballotid={1}".format(i, balid)
        imgpaths = bal2imgs[balid]
        for j, subtuple in enumerate(infotuples):
            if issubclass(type(subtuple), IOError):
                ioerr_imgpaths.append(subtuple.filename)
                continue
            imgpath = imgpaths[j]
            bcs, isflipped, bbs, bbstripes_dict = subtuple
            bc_ul = bcs[0]
            if not bc_ul:
                print "..error on: {0}".format(imgpath)
                err_imgpaths.append(imgpath)
            print "    ({0}) bc={1} isflip={2}".format(j, bc_ul, isflipped)
            img2dec[imgpath] = bc_ul
            img2flip[imgpath] = isflipped

    pdb.set_trace()

if __name__ == '__main__':
    main()
