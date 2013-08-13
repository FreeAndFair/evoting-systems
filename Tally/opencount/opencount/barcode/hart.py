import sys, os, pdb, time, argparse
import cv
import i2of5

def decode_patch(img, n, topbot_pairs, cols=4, debug=False, imgP=None):
    """ Decodes the barcode present in IMG, returns it as a string.
    Input:
        IMG: Either a string (imgpath), or an image object.
        int N: Number of decimals in the barcode.
    Output:
        (str DECODED, tuple BB), where BB is the bounding box around the
        barcode: (x1, y1, w, h)
    """
    if type(img) == str:
        I = cv.LoadImage(img, cv.CV_LOAD_IMAGE_GRAYSCALE)
    else:
        I = img
    return i2of5.decode_i2of5(I, n, topbot_pairs, cols=cols, debug=debug, imgP=imgP)

def decode(imgpath, topbot_pairs, col_sched=(4, 5, 2, 3), debug=False, skipVerify=True):
    """ Given a Hart-style ballot, returns the UPPERLEFT barcode. Will 
    try to detect flipped ballots and correct.
    Input:
        str imgpath:
        list TOPBOT_PAIRS: list of [[IplImage topguard, IplImage botguard], ...].
        bool SKIPVERIFY:
            If True, then don't output BBS/BBSTRIPES_MAP data structures.
            Useful if you don't care about this information, as it takes
            up a lot of memory for large datasets.
    Output:
        (tuple barcodes, bool isflipped, tuple BBS, dict BBSTRIPES_MAP). 
        BARCODES is a tuple of one string (UpperLeft).
        ISFLIPPED is True if we detected the ballot was flipped. 
        BBS is a tuple of tuples: [(x1,y1, w, h), ...]
        BBSTRIPES_MAP maps {str label: [(x1,y1,x2,y2), ...]}
        If SKIPVERIFY was True, then BBS/BBSTRIPES_MAP will be None.
    """
    def check_result(decoded):
        """ UpperLeft has 14 digits, LowerLeft has 12 digits, and
        LowerRight has 10 digits.
        """
        if not decoded or len(decoded) != 14:
            return False
        else:
            test, chk, chk_shouldbe = check_checksum(decoded)
            if not test:
                return False
        return decoded
    # UpperLeft: 15% of width, 30% of height.
    if type(imgpath) == str or type(imgpath) == unicode:
        I = cv.LoadImage(imgpath, cv.CV_LOAD_IMAGE_GRAYSCALE)
    else:
        I = imgpath
    w, h = cv.GetSize(I)
    isflipped = False
    bb_ul = (10, int(round(h*0.03)), int(round(w * 0.13)), int(round(h * 0.23)))
    cv.SetImageROI(I, bb_ul)
    dec_ul, outbb_ul, bbstripes_ul = decode_patch(I, 14, topbot_pairs, cols=col_sched[0],
                                                  debug=debug, imgP=imgpath)
    check = check_result(dec_ul)
    if not check:
        isflipped = True
        tmp = cv.CreateImage((w,h), I.depth, I.channels)
        cv.ResetImageROI(I)
        cv.Flip(I, tmp, flipMode=-1)
        I = tmp
        cv.SetImageROI(I, bb_ul)
        dec_ul, outbb_ul, bbstripes_ul = decode_patch(I, 14, topbot_pairs, cols=col_sched[0],
                                                      debug=debug, imgP=imgpath)
    check_flip = check_result(dec_ul)
    if not check_flip:
        if len(col_sched) == 1:
            return ((None,), isflipped, (outbb_ul,), bbstripes_ul) if skipVerify == False else ((None,), isflipped, None, None)
        else:
            return decode(imgpath, topbot_pairs, col_sched=col_sched[1:], debug=debug, skipVerify=skipVerify)

    if skipVerify:
        return ((dec_ul,), isflipped, None, None)

    bb_out = (int(round(outbb_ul[0] + bb_ul[0])),
              int(round(outbb_ul[1] + bb_ul[1])),
              int(round(outbb_ul[2])),
              int(round(outbb_ul[3])))
    bbstripes_ul_new = {}
    for label, stripebbs in bbstripes_ul.iteritems():
        bbs_new = []
        for bb in stripebbs:
            x1_out = bb[0] + bb_out[0]
            y1_out = bb[1] + bb_out[1]
            bbs_new.append((int(round(x1_out)),
                            int(round(y1_out)),
                            int(round(x1_out + bb[2])), 
                            int(round(y1_out + bb[3]))))
        bbstripes_ul_new[label] = tuple(bbs_new)
    return ((dec_ul,), isflipped, (bb_out,), bbstripes_ul_new)

def interpret_labels(img_bc_labels):
    """
    Input:
        dict IMG_BC_LABELS: {str imgpath: [(bbstripe_i, bc_label_i), ...]}
    Output:
        dict IMG_DECODED_MAP: {str imgpath: str BC}
    """
    img_decoded_map = {}
    for imgpath, tups in img_bc_labels.iteritems():
        tups_sorted = sorted(tups, key=lambda t: t[0])
        bc = []
        whts = []
        blks = []
        # LABEL is WHITE_NARROW, WHITE_WIDE, BLACK_NARROW, BLACK_WIDE
        for i, (idx, label) in enumerate(tups_sorted):
            if i != idx:
                print "Uhoh, problem."
                pdb.set_trace()
            assert i == idx
            if label in (i2of5.WHITE_NARROW, i2of5.WHITE_WIDE):
                whts.append(i2of5.NARROW if label == i2of5.WHITE_NARROW else i2of5.WIDE)
            else:
                blks.append(i2of5.NARROW if label == i2of5.BLACK_NARROW else i2of5.WIDE)
        # Strip out begin/end guards
        whts_noguard = whts[2:-1]
        blks_noguard = blks[2:-2]
        whts_digits = i2of5.bars_to_symbols(whts_noguard)
        blks_digits = i2of5.bars_to_symbols(blks_noguard)
        decoding = ''.join(sum(map(None, blks_digits, whts_digits), ()))
        img_decoded_map[imgpath] = decoding
    return img_decoded_map

def get_sheet(bc):
    return bc[0]
def get_precinct(bc):
    return bc[1:7]
def get_page(bc):
    return int(bc[8])
def get_language(bc):
    '''
    MAP = {'0': 'en',
           '1': 'span',
           '2': 'viet',
           '3': 'cn',
           '4': 'kor'}
    k = bc[9]
    return MAP.get(k, 'lang{0}'.format(k))
    '''
    return bc[9]
def get_party(bc):
    '''
    MAP = {'0': 'nonpartisan',
           '1': 'dem',
           '2': 'lib',
           '3': 'american_indep',
           '4': 'green',
           '5': 'peace',
           '6': 'rep',
           '7': 'americans_elect',
           '8': 'demV2',
           '9': 'american_indepV2'}
    return MAP[bc[11]]
    '''
    return bc[10:12]
def get_checksum(bc):
    return bc[-2:]
def check_checksum(bc):
    def compute_chksum(digits):
         outsum = 1
         w = 82
         for digit in digits:
             outsum = (outsum+digit*w)%97
             w = (w*68)%97
         if outsum == 1:
             return 98
         elif outsum == 0:
             return 97
         return outsum
    chk = compute_chksum(map(int, bc[:-2]))
    chk_shouldbe = int(get_checksum(bc))
    return chk == chk_shouldbe, chk, chk_shouldbe

def get_info(barcodes):
    """ Extracts various semantic meaning(s) from the decoded
    barcodes.
    Input:
        list BARCODES. [bc_i, ...].
    Output:
        dict INFO. Maps {'page': int page, 'party': party_idx, 'sheet': sheet,
                         'language': lang_idx, 'precinct': precinct_idx}
    """
    ul = barcodes[0]
    info = {'sheet': get_sheet(ul), 'precinct': get_precinct(ul),
            'page': get_page(ul), 'language': get_language(ul),
            'party': get_party(ul)}
    return info

def isimgext(f):
    return os.path.splitext(os.path.split(f)[1])[1].lower() in ('.png', '.bmp', '.jpg')
def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("imgsdir", help="Directory of ballot images to \
decode. Can be a single image path.")
    parser.add_argument("--patch", action="store_true",
                        help="Input images have already been cropped to \
the barcode.")
    parser.add_argument("--draw_bbs", metavar="outdir", nargs=1,
                        help="If given, then for each decoded image, \
output a new image in OUTDIR with each detected mark outlined in colored \
rectangles.")
    parser.add_argument("--debug", action="store_true")
    return parser.parse_args()
    
def main():
    args = parse_args()

    imgpaths = []
    if isimgext(args.imgsdir):
        imgpaths.append(args.imgsdir)
    else:
        for dirpath, dirnames, filenames in os.walk(args.imgsdir):
            for imgname in [f for f in filenames if isimgext(f)]:
                imgpaths.append(os.path.join(dirpath, imgname))
    # 1.) Load in top/bot guard pairs.
    topbot_pairs = [[cv.LoadImage(i2of5.TOP_GUARD_IMGP, cv.CV_LOAD_IMAGE_GRAYSCALE),
                     cv.LoadImage(i2of5.BOT_GUARD_IMGP, cv.CV_LOAD_IMAGE_GRAYSCALE)],
                    [cv.LoadImage(i2of5.TOP_GUARD_SKINNY_IMGP, cv.CV_LOAD_IMAGE_GRAYSCALE),
                     cv.LoadImage(i2of5.BOT_GUARD_SKINNY_IMGP, cv.CV_LOAD_IMAGE_GRAYSCALE)]]
    errs = []
    t = time.time()
    if not args.patch:
        for imgpath in imgpaths:
            bcs, isflip, bcloc, bbstripes = decode(imgpath, topbot_pairs, debug=args.debug)
            print '{0}: '.format(imgpath), bcs, isflip, bcloc
            if None in bcs:
                errs.append(imgpath)
                continue
            if args.draw_bbs != None:
                outdir = args.draw_bbs
                imgname = os.path.splitext(os.path.split(imgpath)[1])[0]
                outrootdir = os.path.join(outdir, imgname)
                bc_ul = bcloc[0]
                try: os.makedirs(outrootdir)
                except: pass
                Icolor = cv.LoadImage(imgpath, cv.CV_LOAD_IMAGE_COLOR)
                if isflip:
                    cv.Flip(Icolor, Icolor, flipMode=-1)
                # 1.) First, draw Barcode boundingbox
                pt1 = tuple(map(int, (bc_ul[0], bc_ul[1])))
                pt2 = tuple(map(int, (bc_ul[0]+bc_ul[2], bc_ul[1]+bc_ul[3])))
                cv.Rectangle(Icolor, pt1, pt2,
                             cv.CV_RGB(255, 0, 0), thickness=2)
                Icolor_whiteNarrows = cv.CloneImage(Icolor)
                Icolor_whiteWides = cv.CloneImage(Icolor)
                Icolor_blackNarrows = cv.CloneImage(Icolor)
                Icolor_blackWides = cv.CloneImage(Icolor)
                # 2.) Now, draw stripe boundingboxes
                for bb in bbstripes[i2of5.WHITE_NARROW]:
                    pt1 = tuple(map(int, (bb[0], bb[1])))
                    pt2 = tuple(map(int, (bb[2], bb[3])))
                    cv.Rectangle(Icolor_whiteNarrows, pt1, pt2,
                                 cv.CV_RGB(0, 0, 255), thickness=1)
                for bb in bbstripes[i2of5.WHITE_WIDE]:
                    pt1 = tuple(map(int, (bb[0], bb[1])))
                    pt2 = tuple(map(int, (bb[2], bb[3])))
                    cv.Rectangle(Icolor_whiteWides, pt1, pt2,
                                 cv.CV_RGB(0, 0, 255), thickness=1)
                for bb in bbstripes[i2of5.BLACK_NARROW]:
                    pt1 = tuple(map(int, (bb[0], bb[1])))
                    pt2 = tuple(map(int, (bb[2], bb[3])))
                    cv.Rectangle(Icolor_blackNarrows, pt1, pt2,
                                 cv.CV_RGB(0, 0, 255), thickness=1)
                for bb in bbstripes[i2of5.BLACK_WIDE]:
                    pt1 = tuple(map(int, (bb[0], bb[1])))
                    pt2 = tuple(map(int, (bb[2], bb[3])))
                    cv.Rectangle(Icolor_blackWides, pt1, pt2,
                                 cv.CV_RGB(0, 0, 255), thickness=1)
                outpath0 = os.path.join(outrootdir, 'bc_bb.png')
                outpath1 = os.path.join(outrootdir, 'whiteNarrows.png')
                outpath2 = os.path.join(outrootdir, 'whiteWides.png')
                outpath3 = os.path.join(outrootdir, 'blackNarrows.png')
                outpath4 = os.path.join(outrootdir, 'blackWides.png')
                print '...saving to {0}...'.format(outpath0)
                cv.SaveImage(outpath0, Icolor)
                cv.SaveImage(outpath1, Icolor_whiteNarrows)
                cv.SaveImage(outpath2, Icolor_whiteWides)
                cv.SaveImage(outpath3, Icolor_blackNarrows)
                cv.SaveImage(outpath4, Icolor_blackWides)
    elif args.patch:
        n = args[2]
        decoded = decode_patch(imgpath, n)
    dur = time.time() - t
    print "...Time elapsed: {0} s".format(dur)
    avg_time = dur / len(imgpaths)
    print "Avg. Time per ballot ({0} ballots): {1} s".format(len(imgpaths), avg_time)
    print "    Number of Errors: {0}".format(len(errs))
    print errs
    
if __name__ == '__main__':
    main()
