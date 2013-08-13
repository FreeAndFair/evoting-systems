import sys, os, pickle, time, multiprocessing, random, pdb
from os.path import join as pathjoin

sys.path.append('..')

import scipy.misc, cv

import pixel_reg.shared as shared
import pixel_reg.part_match as part_match
import group_attrs
import partask

GRP_PER_BALLOT = 0
GRP_PER_PARTITION = 1 

def do_digit_group(b2imgs, img2b, partitions_map, partitions_invmap,
                   partition_exmpls, badballotids,
                   img2page, img2flip, attrinfo, digitexemplars_map,
                   digitpatch_outdir, voteddir_root, digpatch2imgpath_outP,
                   mode=GRP_PER_PARTITION):
    """
    Input:
        dict B2IMGS:
        dict IMG2B:
        dict PARTITIONS_MAP:
        dict PARTITIONS_INVMAP:
        dict PARTITIONS_EXMPLS:
        list BADBALLOTIDS: List of quarantined/discarded ballot ids.
        dict IMG2PAGE:
        dict IMG2FLIP: maps {str imgpath: bool isflip}
        dict ATTRINFO: [x1,y1,x2,y2,attrtype,page,numdigits,digitdist]
        dict DIGITEXEMPLARS_MAP: maps {str digitval: [[str regionP, (y1,y2,x1,x2), str digitpatch_i], ...]}
        str DIGITPATCH_OUTDIR: Root dir of extracted digit patches.
        str VOTEDDIR_ROOT: Root dir of voted ballots.
        int MODE:
    Output:
        dict DRESULTS. maps {int ID: [str digitstr, imgpath, [[str digit_i, (x1,y1,x2,y2), score_i, digpatchP_i], ...]]},
            where ID is partitionID/ballotID depending on MODE.
    """
    x1, y1, x2, y2, attrtype, page, numdigits, digitdist = attrinfo
    
    # 0.) Depending on MODE, grab the image paths to work with.
    d_imgpaths = [] # imgpaths with the digit attribute present
    flip_map = {} # maps {str imgpath: bool isflip}
    if mode == GRP_PER_PARTITION:
        for partitionID, ballotIDs in partition_exmpls.iteritems():
            imgpaths = b2imgs[ballotIDs[0]]
            imgpaths_ordered = sorted(imgpaths, key=lambda imP: img2page[imP])
            d_imgpaths.append(imgpaths_ordered[page])
            for imgpath in imgpaths_ordered:
                flip_map[imgpath] = img2flip[imgpath]
    else:
        for ballotID, imgpaths in b2imgs.iteritems():
            if ballotID in badballotids:
                continue
            imgpaths_ordered = sorted(imgpaths, key=lambda imP: img2page[imP])
            d_imgpaths.append(imgpaths_ordered[page])
        flip_map = img2flip

    # 1.) Load the digit exemplars
    digit_ex_imgs = {} # maps {(str digit, str meta): nparray digit_img}
    for digit, exemplars in digitexemplars_map.iteritems():
        for i, (regionP, bb, digitpatch) in enumerate(exemplars):
            I = shared.standardImread(digitpatch, flatten=True)
            digit_ex_imgs[(digit, i)] = I

    # 2.) Invoke digitParse
    bb = (y1, y2, x1, x2)
    rejected_hashes = {}
    accepted_hashes = {}
    # RESULTS: [(imgpath_i, ocrstr_i, imgpatches_i, patchcoords_i, scores_i), ...]
    pm_results = part_match.digitParse(digit_ex_imgs, d_imgpaths, bb, numdigits,
                                       flipmap=flip_map, rejected_hashes=rejected_hashes,
                                       accepted_hashes=accepted_hashes,
                                       hspace=digitdist)
    # 3.) Finally, munge PM_RESULTS into DRESULTS, and also extract
    #     each digit patch into proj.digitpatch_out.
    dresults = {}
    extract_jobs = [] # [[imgpath, (x1,y1,x2,y2), outpath], ...]
    digpatch2imgpath = {} # maps {str digpatchpath: (str imgpath, int idx)}

    for (imgpath, ocrstr, imgpatches, patchcoords, scores) in pm_results:
        ballotid = img2b[imgpath]
        # Recreate directory structure
        rp = os.path.relpath(os.path.abspath(imgpath), os.path.abspath(voteddir_root))

        imgname = os.path.splitext(os.path.split(imgpath)[1])[0]
        if mode == GRP_PER_PARTITION:
            id = partitions_invmap[ballotid]
        else:
            id = ballotid
        entry = []
        for i,digit in enumerate(ocrstr):
            y1, y2, x1, x2 = patchcoords[i]
            digpatchP = pathjoin(digitpatch_outdir, rp, "{0}_dig{1}_{2}.png".format(imgname, digit, i))
            entry.append([digit, (x1,y1,x2,y2), scores[i], digpatchP])
            extract_jobs.append((imgpath, (x1,y1,x2,y2), digpatchP, img2flip[imgpath]))
            digpatch2imgpath[digpatchP] = (imgpath, i)
        row = (ocrstr, imgpath, entry)
        dresults[id] = row

    pickle.dump(digpatch2imgpath, open(digpatch2imgpath_outP, 'wb'),
                pickle.HIGHEST_PROTOCOL)

    print "...Extracting DigitPatches..."
    t = time.time()
    do_extract_digitpatches(extract_jobs)
    dur = time.time() - t
    print "...Finished extracting digit patches ({0} s).".format(dur)

    return dresults

def do_extract_digitpatches(jobs):
    """
    Input:
        list JOBS: [[imgpath, (x1,y1,x2,y2), outpath], ...]
    """
    N = multiprocessing.cpu_count()
    partask.do_partask(extract_digitpatch, jobs, combfn='ignore', N=N)

def extract_digitpatch(jobs):
    for (imgpath, (x1,y1,x2,y2), outpath, isflip) in jobs:
        try:
            os.makedirs(os.path.split(outpath)[0])
        except:
            pass
        I = cv.LoadImage(imgpath, cv.CV_LOAD_IMAGE_UNCHANGED)

        if isflip:
            cv.Flip(I, I, flipMode=-1)

        cv.SetImageROI(I, tuple(map(int, (x1,y1,x2-x1, y2-y1))))
        cv.SaveImage(outpath, I)
    return True
    
def compute_digit_exemplars(proj, LIMIT=100):
    """ Computes multiple digit exemplars, in order to enhance the
    digit grouping.
    Input:
        obj proj
        int LIMIT:
            For each digit, only consider up-to LIMIT images when
            computing exemplars. If None, then consider all images.
    Output:
        A dict, mapping {str digit: [(regionpath_i, (x1,y1,x2,y2), exemplarpath), ...]}
    """
    digit_exemplars_mapP = pathjoin(proj.projdir_path,
                                    proj.digit_exemplars_map)
    # maps {str digit: ((regionpath_i, score_i, bb_i, digitpatchpath_i), ...)}
    digit_exemplars_map = pickle.load(open(digit_exemplars_mapP, 'rb'))

    # 0.) Munge digit_exemplars_map into compatible-format
    mapping = {} # maps {str digit: ((regionpath_i, bb_i), ...)}
    for digit, tuples in digit_exemplars_map.iteritems():
        # TUPLES := [(regionpath, float score, (x1,y1,x2,y2), patchpath), ...]
        dig_exampletuples = []
        if LIMIT == None or len(tuples) <= LIMIT:
            # Consider ALL images
            for (regionpath, score, bb, patchpath) in tuples:
                dig_exampletuples.append((regionpath, bb))
        else:
            # Randomly sample LIMIT images
            dig_exampletuples = [(regionpath, bb) for (regionpath, _, bb, _) in random.sample(tuples, LIMIT)]
        mapping[digit] = dig_exampletuples

    # exemplars := maps {str digit: ((regionpath_i, bb_i), ...)}
    exemplars = group_attrs.compute_exemplars_fullimg(mapping, MAXCAP=10)
    digitmultexemplars_map = {} # maps {str digit: ((regionpath_i, bb_i, patchpath_i), ...)}
    for digit, tuples in exemplars.iteritems():
        for i, (regionpath, bb) in enumerate(tuples):
            y1, y2, x1, x2 = bb
            regionimg = scipy.misc.imread(regionpath) # don't open a grayscale img twice, tends to lighten it
            patch = regionimg[bb[0]:bb[1], bb[2]:bb[3]]
            rootdir = os.path.join(proj.projdir_path,
                                   proj.digitmultexemplars,
                                   digit)
            try:
                os.makedirs(rootdir)
            except:
                pass
            exemplarP = pathjoin(rootdir, '{0}.png'.format(i))
            scipy.misc.imsave(exemplarP, patch)
            digitmultexemplars_map.setdefault(digit, []).append((regionpath, (x1,y1,x2,y2), exemplarP))
    pickle.dump(digitmultexemplars_map,
                open(os.path.join(proj.projdir_path, proj.digitmultexemplars_map), 'wb'))
    return digitmultexemplars_map
