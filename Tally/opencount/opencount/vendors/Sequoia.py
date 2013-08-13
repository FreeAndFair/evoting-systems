import sys, pdb, traceback

try:
    import cPickle as pickle
except ImportError:
    import pickle

import cv

sys.path.append('..')

import barcode.sequoia as sequoia
import grouping.partask as partask, grouping.tempmatch as tempmatch

from Vendor import Vendor

class SequoiaVendor(Vendor):
    def __init__(self, proj):
        self.proj = proj

    def decode_ballots(self, ballots, manager=None, queue=None, skipVerify=True, *args, **kwargs):
        img2decoding, flipmap, mark_bbs_map, err_imgpaths, ioerr_imgpaths, backsmap = partask.do_partask(_decode_ballots,
                                                                                                         ballots,
                                                                                                         _args=(sequoia.ZERO_IMGPATH,
                                                                                                                sequoia.ONE_IMGPATH,
                                                                                                                sequoia.SIDESYM_IMGPATH,
                                                                                                                self.proj.num_pages,
                                                                                                                skipVerify),
                                                                                                         combfn=_combfn,
                                                                                                         init=({}, {}, {}, [], [], {}),
                                                                                                         manager=manager,
                                                                                                         pass_queue=queue,
                                                                                                         N=None)
        # BACKSMAP: maps {int ballotID: [imgpath_i, ...]}. Stores all backside imagepaths for each ballotid
        self.backsmap = backsmap
        return (img2decoding, flipmap, mark_bbs_map, err_imgpaths, ioerr_imgpaths)

    def partition_ballots(self, img2decoding, verified_results, manual_labeled):
        """
        Input:
            dict VERIFIED_RESULTS: maps {markval, [(imgpath, (x1,y1,x2,y2), userdata), ...]}
                If None, then skipVerify was True.
            dict MANUAL_LABELED: maps {imgpath: [decoding_left, decoding_right]}
        Note: imgpaths not in VERIFIED_RESULTS but in FLIPMAP are back sides.
        Output:
            (dict PARTITIONS, dict IMG2DECODING, dict IMGINFO_MAP)
        """
        partitions = {}
        imginfo_map = {}

        if verified_results:
            img2decoding = {}            
            decodings_tmp = {} # maps {imgpath: [(left/right, y1, digitval), ...]}
            for markval, tups in verified_results.iteritems():
                digitval = '1' if markval == sequoia.MARK_ON else '0'
                for (imgpath, bb, side) in tups:
                    decodings_tmp.setdefault(imgpath, []).append((side, bb[1], digitval))

            for imgpath, tups in decodings_tmp.iteritems():
                # group by LEFT/RIGHT, sort by y1 coordinate
                left = [(y1, digitval) for (side, y1, digitval) in tups if side == sequoia.LEFT]
                right = [(y1, digitval) for (side, y1, digitval) in tups if side == sequoia.RIGHT]
                left_sorted = sorted(left, key=lambda t: t[0])
                right_sorted = sorted(right, key=lambda t: t[0])
                left_decoding = ''.join([val for (y1, val) in left_sorted])
                right_decoding = ''.join([val for (y1, val) in right_sorted])
                decoding = (left_decoding, right_decoding)
                img2decoding[imgpath] = decoding
                imginfo = get_imginfo(decoding)
                imginfo['page'] = 0
                imginfo_map[imgpath] = imginfo
        else:
            for imgpath, decoding_tuple in img2decoding.iteritems():
                imginfo = get_imginfo(decoding_tuple)
                imginfo['page'] = 0
                imginfo_map[imgpath] = imginfo

        for imgpath, decoding in manual_labeled.iteritems():
            # TODO: Introduce a non-hacky way to manually indicate that
            # an image is a back-side, rather than entering in "0,".
            # TODO: Only supports double-sided elections.
            if decoding[0] == "0" and decoding[1] == "":
                decoding = ("BACK", "BACK")
                info = get_imginfo(decoding)
                info['page'] = 1
            else:
                info = get_imginfo(decoding)
                info['page'] = 0
            img2decoding[imgpath] = decoding
            imginfo_map[imgpath] = info
        for ballotid, backimgpaths in self.backsmap.iteritems():
            for imgpath in backimgpaths:
                # IMGPATH is a back-side image.
                imginfo = {'page': 1}
                imginfo_map[imgpath] = imginfo
                img2decoding[imgpath] = ("BACK", "BACK")  # Signal for backside"

        img2bal = pickle.load(open(self.proj.image_to_ballot, 'rb'))
        bal2imgs = pickle.load(open(self.proj.ballot_to_images, 'rb'))
        decoding2partition = {} # maps {(dec0, dec1, ...): int partitionID}
        curPartitionID = 0
        history = set()
        for imgpath, decoding in img2decoding.iteritems():
            ballotid = img2bal[imgpath]
            if ballotid in history:
                continue
            imgpaths = bal2imgs[ballotid]
            try:
                imgpaths_ordered = sorted(imgpaths, key=lambda imP: imginfo_map[imP]['page'])
            except Exception as e:
                traceback.print_exc()
                dumped = {'img2decoding': img2decoding,
                          'imgpath': imgpath,
                          'decoding': decoding,
                          'ballotid': ballotid,
                          'imgpaths': imgpaths,
                          'imginfo_map': imginfo_map,
                          'backsmap': self.backsmap,
                          'verified_results': verified_results,
                          'manual_labeled': manual_labeled,
                          'history': history,
                          'curPartitionID': curPartitionID}
                pickle.dump(dumped, open('crash_dumpstate.p', 'wb'))
                print "CRASH -- dumping relevant state to: 'crash_dumpstate.p'"
                pdb.set_trace()
            # Only the front-page has barcode information
            decoding = img2decoding[imgpaths_ordered[0]]
            partitionid = decoding2partition.get(decoding, None)
            if partitionid == None:
                decoding2partition[decoding] = curPartitionID
                partitionid = curPartitionID
                curPartitionID += 1
            partitions.setdefault(partitionid, []).append(ballotid)
            history.add(ballotid)
        return partitions, img2decoding, imginfo_map

    def __repr__(self):
        return 'SequoiaVendor()'
    def __str__(self):
        return 'SequoiaVendor()'

def is_valid_decodings(decodings):
    """
    Input:
        list DECODINGS: [str barcode_upperleft, str barcode_upperright]
    Output:
        True/False.
    """
    if not decodings or len(decodings) != 2:
        return False
    if decodings[0] == '0' and decodings[1] == '':
        return True # Hacky signal for 'back side' in manual label: '0,'
    if len(decodings[0]) != 8 or len(decodings[1]) != 8:
        return False
    return True

def get_imginfo(decodings):
    """ Note: barcode values are output top-to-down.
    """
    # TODO: Actually output the party/ballot-layout-id.
    return {}

def _combfn(a, b):
    img2dec_a, flipmap_a, mark_bbs_map_a, errs_imgpaths_a, ioerr_imgpaths_a, backsmap_a = a
    img2dec_b, flipmap_b, mark_bbs_map_b, errs_imgpaths_b, ioerr_imgpaths_b, backsmap_b = b
    img2dec_out = dict(img2dec_a.items() + img2dec_b.items())
    flipmap_out = dict(flipmap_a.items() + flipmap_b.items())
    mark_bbs_map_out = mark_bbs_map_a
    for marktype, tups in mark_bbs_map_b.iteritems():
        mark_bbs_map_out.setdefault(marktype, []).extend(tups)
    errs_imgpaths_out = errs_imgpaths_a + errs_imgpaths_b
    ioerrs_imgpaths_out = ioerr_imgpaths_a + ioerr_imgpaths_b
    backs_map_out = dict(backsmap_a.items() + backsmap_b.items())
    return (img2dec_out, flipmap_out, mark_bbs_map_out, errs_imgpaths_out, ioerrs_imgpaths_out, backs_map_out)

def _decode_ballots(ballots, (template_path_zero, template_path_one, sidesym_path, num_pages, skipVerify), queue=None):
    """
    Input:
        dict BALLOTS: {int ballotID: [imgpath_i, ...]}
        int NUM_PAGES:
            The number of pages this election has. Only supports 1, or
            multiples of 2 (assuming front/back pairs).
    Output:
        (dict img2decoding, dict flipmap, dict mark_bbs, list err_imgpaths, list ioerr_imgpaths, dict backsmap)
    Since backsides do not really have barcodes, and I detect the 
    front/back by the ISIDESYM mark, back sides are handled differently.
    If an image I is found to be a backside, it will be added to the
    FLIPMAP, but not to the MARK_BBS. 
    The SequoiaVendor object will be responsible for recognizing that
    imgpaths not present in the VERIFIED_RESULTS, but present in the
    FLIPMAP, are back-side images. 
    """
    flipmap = {}
    mark_bbs_map = {} # maps {str "ON"/"OFF": [(imgpath, (x1,y1,x2,y2), userdata), ...]}
    err_imgpaths = set()
    ioerr_imgpaths = set()
    img2decoding = {}
    Itemp0 = cv.LoadImage(template_path_zero, cv.CV_LOAD_IMAGE_GRAYSCALE)
    Itemp1 = cv.LoadImage(template_path_one, cv.CV_LOAD_IMAGE_GRAYSCALE)
    IsymA = cv.LoadImage(sequoia.SYMA_IMGPATH, cv.CV_LOAD_IMAGE_GRAYSCALE)
    IsymB = cv.LoadImage(sequoia.SYMB_IMGPATH, cv.CV_LOAD_IMAGE_GRAYSCALE)
    IsymC = cv.LoadImage(sequoia.SYMC_IMGPATH, cv.CV_LOAD_IMAGE_GRAYSCALE)
    IsymD = cv.LoadImage(sequoia.SYMD_IMGPATH, cv.CV_LOAD_IMAGE_GRAYSCALE)
    IsymE = cv.LoadImage(sequoia.SYME_IMGPATH, cv.CV_LOAD_IMAGE_GRAYSCALE)
    # Rescale to current image resolution
    exmpl_imgsize = cv.GetSize(cv.LoadImage(ballots.values()[0][0], cv.CV_LOAD_IMAGE_UNCHANGED))
    if exmpl_imgsize != (sequoia.ORIG_IMG_W, sequoia.ORIG_IMG_H):
        print "...rescaling template patches to match current resolution..."
        Itemp0 = sequoia.rescale_img(Itemp0, sequoia.ORIG_IMG_W, sequoia.ORIG_IMG_H,
                                     exmpl_imgsize[0], exmpl_imgsize[1])
        Itemp1 = sequoia.rescale_img(Itemp1, sequoia.ORIG_IMG_W, sequoia.ORIG_IMG_H,
                                     exmpl_imgsize[0], exmpl_imgsize[1])
        IsymA = sequoia.rescale_img(IsymA, sequoia.ORIG_IMG_W, sequoia.ORIG_IMG_H,
                                    exmpl_imgsize[0], exmpl_imgsize[1])
        IsymB = sequoia.rescale_img(IsymB, sequoia.ORIG_IMG_W, sequoia.ORIG_IMG_H,
                                    exmpl_imgsize[0], exmpl_imgsize[1])
        IsymC = sequoia.rescale_img(IsymC, sequoia.ORIG_IMG_W, sequoia.ORIG_IMG_H,
                                    exmpl_imgsize[0], exmpl_imgsize[1])
        IsymD = sequoia.rescale_img(IsymD, sequoia.ORIG_IMG_W, sequoia.ORIG_IMG_H,
                                    exmpl_imgsize[0], exmpl_imgsize[1])
        IsymE = sequoia.rescale_img(IsymE, sequoia.ORIG_IMG_W, sequoia.ORIG_IMG_H,
                                    exmpl_imgsize[0], exmpl_imgsize[1])

    Itemp0 = tempmatch.smooth(Itemp0, 3, 3, bordertype='const', val=255.0)
    Itemp1 = tempmatch.smooth(Itemp1, 3, 3, bordertype='const', val=255.0)
    IsymA = tempmatch.smooth(IsymA, 3, 3, bordertype='const', val=255.0)
    IsymB = tempmatch.smooth(IsymB, 3, 3, bordertype='const', val=255.0)
    IsymC = tempmatch.smooth(IsymC, 3, 3, bordertype='const', val=255.0)
    IsymD = tempmatch.smooth(IsymD, 3, 3, bordertype='const', val=255.0)
    IsymE = tempmatch.smooth(IsymE, 3, 3, bordertype='const', val=255.0)
    backsmap = {} # maps {ballotid: [backpath_i, ...]}

    def mygauge_tick(N=1):
        """ Add N ticks to the progress bar. """
        for _ in xrange(N):
            queue.put(True)

    if num_pages == 1:
        return handle_singleside(ballots, Itemp0, Itemp1, IsymA, IsymB, IsymC, IsymD, IsymE, queue)
    else:
        for ballotid, imgpaths in ballots.iteritems():
            fronts, backs = [], []
            for (imgpath0, imgpath1) in by_n_gen(imgpaths, 2):
                is_ioerror = False
                try:
                    I0 = cv.LoadImage(imgpath0, cv.CV_LOAD_IMAGE_GRAYSCALE)
                except IOError as e:
                    print 'IOERROR:', imgpath0
                    ioerr_imgpaths.add(imgpath0)
                    is_ioerror = True
                try:
                    I1 = cv.LoadImage(imgpath1, cv.CV_LOAD_IMAGE_GRAYSCALE)
                except IOError as e:
                    print 'IOERROR:', imgpath1
                    ioerr_imgpaths.add(imgpath1)
                    is_ioerror = True
                if is_ioerror:
                    mygauge_tick(N=2)
                    continue

                side0, isflip0 = sequoia.get_side(I0, IsymA, IsymB, IsymC, IsymD, IsymE)
                side1, isflip1 = sequoia.get_side(I1, IsymA, IsymB, IsymC, IsymD, IsymE)
                if side0 == None and side1 == None:
                    # Something crazy happened, run!
                    err_imgpaths.add(imgpath0)
                    err_imgpaths.add(imgpath1)
                    if queue:
                        mygauge_tick(N=2)
                    print "Craziness here, run!"
                    continue
                if side0 != None:
                    flipmap[imgpath0] = isflip0
                if side1 != None:
                    flipmap[imgpath1] = isflip1
                frontside = None
                if side0 == 0:
                    Ifront = I0
                    frontside = 0
                    imP_front = imgpath0
                    cv.ResetImageROI(Ifront)
                    if isflip0:
                        cv.Flip(Ifront, Ifront, flipMode=-1)
                else:
                    Ifront = I1
                    frontside = 1
                    imP_front = imgpath1
                    cv.ResetImageROI(Ifront)
                    if isflip1:
                        cv.Flip(Ifront, Ifront, flipMode=-1)
                decodings, mark_locs = sequoia.decode(Ifront, Itemp0, Itemp1, _imgpath=imP_front)
                cv.ResetImageROI(Ifront)
                if decodings == None:
                    # Something crazy happened.
                    err_imgpaths.add(imgpath0)
                    err_imgpaths.add(imgpath1)
                    if queue:
                        mygauge_tick(N=2)
                    print "Craziness here, decodings == None"
                    continue
                elif len(decodings[0]) != 8 or len(decodings[1]) != 8:
                    err_imgpaths.add(imgpath0)
                    err_imgpaths.add(imgpath1)
                else:
                    img2decoding[imP_front] = decodings
                    if frontside == 0 and side1 == None:
                        # imgpath1 must be an empty backside.
                        backs.append(imgpath1)
                        flipmap[imgpath1] = False # Anything is fine
                    elif frontside == 1 and side0 == None:
                        # imgpath 0 must be an empty backside.
                        backs.append(imgpath0)
                        flipmap[imgpath0] = False
                    elif frontside == 0:
                        backs.append(imgpath1)
                    elif frontside == 1:
                        backs.append(imgpath0)
                    if not skipVerify:
                        for marktype, tups in mark_locs.iteritems():
                            mark_bbs_map.setdefault(marktype, []).extend(tups)
                    fronts.append(imgpath0)
                if queue: 
                    mygauge_tick(N=2)
            backsmap[ballotid] = backs

        return img2decoding, flipmap, mark_bbs_map, list(err_imgpaths), list(ioerr_imgpaths), backsmap

def handle_singleside(ballots, Itemp0, Itemp1, IsymA, IsymB, IsymC, IsymD, IsymE,
                      queue, skipVerify):
    """ Do decoding for single-sided elections. Don't do the arm-tangly
    accounting-for-back-sides here - instead, if a backside seems to show
    up, just mark it as an error and move on.
    """
    img2decoding = {}
    flipmap = {}
    mark_bbs_map = {} # maps {str "ON"/"OFF": [(imgpath, (x1,y1,x2,y2), userdata), ...]}
    err_imgpaths = set()
    ioerr_imgpaths = set()
    backsmap = {} # maps {ballotid: [backpath_i, ...]}
    for ballotid, imgpaths in ballots.iteritems():
        imgpath = imgpaths[0]
        is_ioerror = False
        try:
            I0 = cv.LoadImage(imgpath, cv.CV_LOAD_IMAGE_GRAYSCALE)
        except IOError as e:
            print 'IOERROR:', imgpath
            ioerr_imgpaths.add(imgpath)
            is_ioerror = True

        if is_ioerror:
            continue

        side0, isflip0 = sequoia.get_side(I0, IsymA, IsymB, IsymC, IsymD, IsymE)
        if side0 == None or side0 == 1:
            # Something crazy happened, run!
            err_imgpaths.add(imgpath)
            if queue:
                queue.put(True)
            continue

        flipmap[imgpath] = isflip0
        Ifront = I0
        cv.ResetImageROI(Ifront)
        if isflip0:
            cv.Flip(Ifront, Ifront, flipMode=-1)

        decodings, mark_locs = sequoia.decode(Ifront, Itemp0, Itemp1, _imgpath=imgpath)
        cv.ResetImageROI(Ifront)
        if decodings == None:
            # Something crazy happened.
            err_imgpaths.add(imgpath)
            if queue:
                queue.put(True)
            continue
        elif len(decodings[0]) != 8 or len(decodings[1]) != 8:
            err_imgpaths.add(imgpath)
        else:
            img2decoding[imgpath] = decodings
            if not skipVerify:
                for marktype, tups in mark_locs.iteritems():
                    mark_bbs_map.setdefault(marktype, []).extend(tups)
        if queue: 
            queue.put(True)

    return img2decoding, flipmap, mark_bbs_map, list(err_imgpaths), list(ioerr_imgpaths), backsmap

def by_n_gen(seq, n):
    i = 0
    while i < len(seq):
        toreturn = seq[i:i+n]
        yield toreturn
        i += n
