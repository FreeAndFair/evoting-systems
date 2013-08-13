import os, sys, traceback, pdb
try:
    import cPickle as pickle
except:
    import pickle
from os.path import join as pathjoin

import cv    
import diebold_raw

sys.path.append('..')
import grouping.partask as partask

from Vendor import Vendor

from diebold_raw import get_checksum, get_precinct, get_cardnum, get_seqnum, \
    get_startbit, get_day, get_month, get_year, get_electiontype, get_endercode, \
    get_page

# Get this script's directory. Necessary to know this information
# since the current working directory may not be the same as where
# this script lives (which is important for loading resources like
# imgs)
try:
    MYDIR = os.path.abspath(os.path.dirname(__file__))
except NameError:
    # This script is being run directly
    MYDIR = os.path.abspath(sys.path[0])

TEMPLATE_PATH = pathjoin(MYDIR, 'diebold_mark.png')
COLMARK_PATH = pathjoin(MYDIR, 'diebold_colmark.png')

ON = 'ON'
OFF = 'OFF'

class DieboldVendor(Vendor):
    def __init__(self, proj):
        self.proj = proj

    def decode_ballots(self, ballots, manager=None, queue=None, skipVerify=True, *args, **kwargs):
        return partask.do_partask(_decode_ballots,
                                  ballots,
                                  _args=(TEMPLATE_PATH, COLMARK_PATH, skipVerify),
                                  combfn=_combfn,
                                  init=({}, {}, {}, [], []),
                                  manager=manager,
                                  pass_queue=queue,
                                  N=None)

    def partition_ballots(self, img2decoding, verified_results, manual_labeled):
        """
        Input:
            dict VERIFIED_RESULTS:
                If None, then skipVerify was True.
            dict MANUAL_LABELED: {str imgpath: (str bc,)}
        Output:
            (dict PARTITIONS, dict IMG2DECODING, dict IMGINFO_MAP)
        """
        partitions = {}
        imginfo_map = {}

        if verified_results:
            img2decoding = {}
            decodings_tmp = {} # maps {imgpath: list}
            for markval, tups in verified_results.iteritems():
                digitval = '1' if markval == ON else '0'
                for (imgpath, bb, idx) in tups:
                    decodings_tmp.setdefault(imgpath, []).append((bb[0], digitval))

            for imgpath, tups in decodings_tmp.iteritems():
                # sort by x1 coordinate
                tups_sorted = sorted(tups, key=lambda t: t[0])
                decoding = ''.join([val for (x1, val) in tups_sorted])
                img2decoding[imgpath] = (decoding,)
                imginfo = get_imginfo(decoding)
                imginfo_map[imgpath] = imginfo
        else:
            for imgpath, decoding_tuple in img2decoding.iteritems():
                imginfo_map[imgpath] = get_imginfo(decoding_tuple[0])
        for imgpath, decoding_tuple in manual_labeled.iteritems():
            img2decoding[imgpath] = decoding_tuple
            imginfo_map[imgpath] = get_imginfo(decoding_tuple[0])

        img2bal = pickle.load(open(self.proj.image_to_ballot))
        bal2imgs = pickle.load(open(self.proj.ballot_to_images))
        decoding2partition = {} # maps {(dec0, dec1, ...): int partitionID}
        curPartitionID = 0
        history = set()
        for imgpath, decoding_tuple in img2decoding.iteritems():
            ballotid = img2bal[imgpath]
            if ballotid in history:
                continue
            imgpaths = bal2imgs[ballotid]
            imgpaths_ordered = sorted(imgpaths, key=lambda imP: imginfo_map[imP]['page'])
            decodings_ordered = tuple([img2decoding[imP] for imP in imgpaths_ordered])
            partitionid = decoding2partition.get(decodings_ordered, None)
            if partitionid == None:
                decoding2partition[decodings_ordered] = curPartitionID
                partitionid = curPartitionID
                curPartitionID += 1
            partitions.setdefault(partitionid, []).append(ballotid)
            history.add(ballotid)
        
        return partitions, img2decoding, imginfo_map
    
    def __repr__(self):
        return 'DieboldVendor()'
    def __str__(self):
        return 'DieboldVendor()'

def get_imginfo(decoding):
    if get_page(decoding) == 0:
        return {'checksum': get_checksum(decoding),
                'precinct': get_precinct(decoding),
                'cardnum': get_cardnum(decoding),
                'seqnum': get_seqnum(decoding),
                'startbit': get_startbit(decoding),
                'page': 0}
    else:
        return {'election_day': get_day(decoding),
                'election_month': get_month(decoding),
                'election_year': get_year(decoding),
                'election_type': get_electiontype(decoding),
                'endercode': get_endercode(decoding),
                'page': 1}

def _combfn(a, b):
    img2dec_a, flipmap_a, mark_bbs_map_a, errs_imgpaths_a, ioerrs_a = a
    img2dec_b, flipmap_b, mark_bbs_map_b, errs_imgpaths_b, ioerrs_b = b
    img2dec_out = dict(img2dec_a.items() + img2dec_b.items())
    flipmap_out = dict(flipmap_a.items() + flipmap_b.items())
    mark_bbs_map_out = mark_bbs_map_a
    for marktype, tups in mark_bbs_map_b.iteritems():
        mark_bbs_map_out.setdefault(marktype, []).extend(tups)
    errs_imgpaths_out = errs_imgpaths_a + errs_imgpaths_b
    ioerrs_out = ioerrs_a + ioerrs_b
    return (img2dec_out, flipmap_out, mark_bbs_map_out, errs_imgpaths_out, ioerrs_out)

def _decode_ballots(ballots, (template_path, colpath, skipVerify), queue=None):
    """
    Input:
        dict BALLOTS: {int ballotID: [imgpath_i, ...]}
    Output:
        (dict flipmap, dict mark_bbs, list err_imgpaths)
    """
    flipmap = {}
    mark_bbs_map = {}
    err_imgpaths = []
    ioerr_imgpaths = []
    Imark = cv.LoadImage(template_path, cv.CV_LOAD_IMAGE_GRAYSCALE)
    Icol = cv.LoadImage(colpath, cv.CV_LOAD_IMAGE_GRAYSCALE)
    w_cur, h_cur = cv.GetSize(cv.LoadImage(ballots[ballots.keys()[0]][0], cv.CV_LOAD_IMAGE_UNCHANGED))
    W_ORIG, H_ORIG = diebold_raw.SIZE_ORIG
    h_gap_cur = diebold_raw.HORIZ_GAP
    w_mark, h_mark = diebold_raw.WIDTH_MARK, diebold_raw.HEIGHT_MARK
    if w_cur != W_ORIG or h_cur != H_ORIG:
        c = w_cur / float(W_ORIG)
        print "...Detected current image resolution {0} differs from \
original resolution {1}. Rescaling Imark, Icol, H_GAP accordingly...".format((w_cur, h_cur),
                                                                             (W_ORIG, H_ORIG))
        Imark = diebold_raw.rescale_img(Imark, c)
        Icol = diebold_raw.rescale_img(Icol, c)
        h_gap_cur = int(round(h_gap_cur * c))
        w_mark = int(round(w_mark * c))
        h_mark = int(round(h_mark * c))

    img2decoding = {}
    for ballotid, imgpaths in ballots.iteritems():
        for imgpath in imgpaths:
            try:
                decoding, isflip, bbs = diebold_raw.decode(imgpath, Imark, Icol, H_GAP=h_gap_cur,
                                                           W_MARK=w_mark, H_MARK=h_mark)
            except IOError as e:
                ioerr_imgpaths.append(imgpath)
                continue
            if decoding == None:
                err_imgpaths.append(imgpath)
            else:
                flipmap[imgpath] = isflip
                if not skipVerify:
                    # sort by x1 coordinate, left-to-right
                    bbs = sorted(bbs, key=lambda t: t[0])
                    for i, markval in enumerate(decoding):
                        MYVAL = ON if markval == '1' else OFF
                        mark_bbs_map.setdefault(MYVAL, []).append((imgpath, bbs[i], None))
                img2decoding[imgpath] = (decoding,)
            if queue:
                queue.put(True)

    return img2decoding, flipmap, mark_bbs_map, err_imgpaths, ioerr_imgpaths
