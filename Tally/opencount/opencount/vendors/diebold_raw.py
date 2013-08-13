import os, sys, time, pdb, traceback, math, pickle
import cv, numpy as np, scipy.stats

import scan_bars
sys.path.append('..')
import grouping.tempmatch as tempmatch
from grouping.verify_overlays_new import iplimage2np

try:
    import matplotlib.pyplot as plt
except:
    pass

MARKFULL_PATH = 'diebold_mark.png'
COLMARK_PATH = 'diebold_colmark.png'

# HORIZ_GAP := Num. pixels between each mark in the barcode
HORIZ_GAP = 7

# WIDTH_MARK, HEIGHT_MARK := Dimensions of a mark
WIDTH_MARK = 28
HEIGHT_MARK = 7

# Image Dimension (w,h) of ballot that MARKFULL_PATH/COLMARK_PATH were
# extracted from. Used to re-scale these exemplar images to generalize to
# other image resolutions, in addition to scaling HORIZ_GAP, WIDTH_MARK,
# HEIGHT_MARK
SIZE_ORIG = (1280, 2104)

PIX_ON_OFF_RATIO = 0.7 # Max. allowable ratio (PIX_ON / PIX_OFF)

DEBUG = False
DEBUG_SAVEIMGS = False

DEBUG_SKIP_FLIP = False

# For experiments.
EXP_PARAMS = False
GLOB_PARAMS_ = None # Stores {"PIX_ON": [float p, ...], "PIX_OFF": [float p, ...]}

def print_dbg(*args):
    if DEBUG == True:
        for x in args:
            print x,
        print

def decode(imgpath, markpath, colpath, H_GAP=HORIZ_GAP,
           W_MARK=WIDTH_MARK, H_MARK=HEIGHT_MARK):
    decoding, isflip, bbs = decode_robust_v2(imgpath, markpath, colpath, H_GAP=H_GAP,
                                             W_MARK=W_MARK, H_MARK=H_MARK)
    if decoding != None:
        bbs = sorted(bbs, key=lambda t: t[0])
        # Strip off the left/right column marks (always '1')
        decoding = decoding[1:-1]
        bbs = bbs[1:-1]
    return decoding, isflip, bbs

def decode_robust_v2(imgpath, markpath, colpath, H_GAP=7,
                     W_MARK=WIDTH_MARK, H_MARK=HEIGHT_MARK):
    if type(markpath) in (str, unicode):
        markfull = cv.LoadImage(markpath, cv.CV_LOAD_IMAGE_GRAYSCALE)
    else:
        markfull = markpath
    if type(colpath) in (str, unicode):
        Icol = cv.LoadImage(colpath, cv.CV_LOAD_IMAGE_GRAYSCALE)
    else:
        Icol = colpath

    # In some elections (SLO), the first/last bits (ignoring the guard marks)
    # are significantly cutoff -- so, allow additional slack on these marks
    # via the IDX2TOL dict. (first bit is idx '1', last bit is idx '32')
    idx2tol = {1: 0.25,
               32: 0.25}

    decoding, isflip, bbs = decode_v2_wrapper(imgpath, markfull, Icol, H_GAP=H_GAP,
                                              W_MARK=W_MARK, H_MARK=H_MARK, idx2tol=idx2tol)
    return decoding, isflip, bbs

def compute_border(A):
    """ Determines if the image contains rows/cols that are all black. """
    h, w = A.shape
    for i1 in xrange(h):
        thesum = np.sum(A[i1])
        if thesum != 0:
            break
    for i2 in xrange(h-1, -1, -1):
        thesum = np.sum(A[i2])
        if thesum != 0:
            break
    for j1 in xrange(w):
        thesum = np.sum(A[:,j1])
        if thesum != 0:
            break
    for j2 in xrange(w-1, -1, -1):
        thesum = np.sum(A[:,j2])
        if thesum != 0:
            break
    return i1, h - i2, j1, w - j2

def decode_v2_wrapper(imgpath, markpath, Icol, H_GAP=7,
                      W_MARK=WIDTH_MARK, H_MARK=HEIGHT_MARK, idx2tol=None):
    I = cv.LoadImage(imgpath, cv.CV_LOAD_IMAGE_GRAYSCALE)
    result = decode_v2(I, markpath, Icol, False, _imgpath=imgpath, H_GAP=H_GAP,
                       W_MARK=W_MARK, H_MARK=H_MARK, idx2tol=idx2tol)
    if result == None and not DEBUG_SKIP_FLIP:
        print_dbg("...Trying FLIP...")
        cv.ResetImageROI(I)
        result = decode_v2(I, markpath, Icol, True, _imgpath=imgpath, H_GAP=H_GAP,
                           W_MARK=W_MARK, H_MARK=H_MARK, idx2tol=idx2tol)
    
    if result == None:
        return None, None, None
    else:
        decoding, isflip, bbs_out = result
        return (decoding, isflip, bbs_out)

def decode_v2(imgpath, markpath, Icol, isflip, _imgpath=None, H_GAP=7,
              W_MARK=WIDTH_MARK, H_MARK=HEIGHT_MARK, idx2tol=None):
    if type(imgpath) in (str, unicode):
        I = cv.LoadImage(imgpath, cv.CV_LOAD_IMAGE_GRAYSCALE)
    else:
        I = imgpath
    if type(markpath) in (str, unicode):
        Imark = cv.LoadImage(markpath, cv.CV_LOAD_IMAGE_GRAYSCALE)
    else:
        Imark = markpath

    if isflip:
        cv.Flip(I, I, -1)

    # Remove the black border from the ballot
    i1_blk, i2_blk, j1_blk, j2_blk = compute_border(iplimage2np(I))
    if DEBUG_SAVEIMGS:
        print_dbg("<><><><> Saving '_I_noblkborder_pre.png' <><><><>")
        cv.SaveImage("_I_noblkborder_pre.png", I)
    shift_roi(I, j1_blk, i1_blk, cv.GetSize(I)[0]-(j1_blk+j2_blk), cv.GetSize(I)[1]-(i1_blk+i2_blk))

    if DEBUG_SAVEIMGS:
        print_dbg("<><><><> Saving '_I_noblkborder.png' <><><><>")
        cv.SaveImage("_I_noblkborder.png", I)
        pdb.set_trace()

    w, h = cv.GetSize(I)
    w_markfull, h_markfull = cv.GetSize(Imark)

    bbs_middle = ((w * 0.15, 0.947 * h,
                   (w-1) - (w*0.15),
                   (0.97 * h)),
                  (w * 0.15, 0.945 * h,
                   (w-1) - (w*0.15),
                   (0.995 *h)),
                  (w * 0.1, 0.93 * h,
                   (w-1) - (w*0.1),
                   (0.995 * h)))

    theta = estimate_ballot_rot(I, Imark, bbs_middle)
    if theta == None:
        print_dbg("Warning: THETA was None.")
        return None
    else:
        print_dbg("==== Theta={0}".format(theta))
    
    bbs_rough = ((0, 0.96 * h,
                  (w-1), (0.985 * h)),
                 (0, 0.93 * h,
                  (w-1), (0.965 * h)),
                 (0, 0.97 * h,
                  (w-1), (0.995 * h)))
    result = decoder_v2_helper(I, Icol, bbs_rough, w_markfull, h_markfull, isflip,
                               H_GAP, theta, 
                               i1_blk, i2_blk, j1_blk, j2_blk,
                               imgpath=_imgpath,
                               W_MARK=W_MARK, H_MARK=H_MARK,
                               idx2tol=idx2tol)
    return result

def find_col_x1(I, Icol, bb, K=3, AX=0.2, AY=0.2, T=0.9):
    """ Tries to find the column of marks on I, using ICOL as a ref.
    image in template matching.
    """
    roi_prev = cv.GetImageROI(I)
    shift_roi(I, bb[0], bb[1], bb[2]-bb[0], bb[3]-bb[1])

    w_A, h_A = cv.GetSize(Icol)
    w_I, h_I = cv.GetSize(I)
    M = cv.CreateMat(h_I - h_A + 1, w_I - w_A + 1, cv.CV_32F)
    cv.MatchTemplate(I, Icol, M, cv.CV_TM_CCOEFF_NORMED)
    if DEBUG_SAVEIMGS:
        M_np = np.array(M)
        import scipy.misc
        print_dbg("<><><><> Saving '_Mbase.png' <><><><>"); cv.SaveImage("_Mbase.png", I)
        print_dbg("<><><><> Saving '_M.png' <><><><>"); scipy.misc.imsave("_M.png", M)
        pdb.set_trace()
    cv.SetImageROI(I, roi_prev)
    i = 0
    xs = []
    _xamt, _yamt = int(round(AX * w_A)), int(round(AY * h_A))
    while i < K:
        minResp, maxResp, minLoc, maxLoc = cv.MinMaxLoc(M)
        if maxResp < T:
            break
        x, y = maxLoc
        # Find the /leftmost/ match: don't find a match in the middle
        # of a column.
        while M[y,x] >= T:
            x -= 1
        xs.append((x + bb[0]))
        _x1 = max(1, x - _xamt)
        _x2 = max(1, x + _xamt)
        _y1 = max(1, y - _yamt)
        _y2 = max(1, y + _yamt)
        M[_y1:_y2, _x1:_x2] = -1.0
        i += 1
    if not xs:
        return None
    elif len(xs) == 1:
        return xs[0]
    return np.median(xs)

def decoder_v2_helper(I, Icol, bbs_rough, w_markfull, h_markfull, isflip, H_GAP, theta, 
                      i1_blk, i2_blk, j1_blk, j2_blk,
                      imgpath=None, find_col=True,
                      W_MARK=WIDTH_MARK, H_MARK=HEIGHT_MARK,
                      idx2tol=None):
    result = None
    roi_prev = cv.GetImageROI(I)
    w, h = cv.GetSize(I)

    if find_col:
        w, h = cv.GetSize(I)
        bb_left = (0.0, 0.86 * h, 0.06 * w, h-1)
        bb_right = ((w-1) - (0.06*w), 0.86 * h, w-1, h-1)
        if DEBUG_SAVEIMGS:
            print_dbg("<><><><> Saving '_Inocolflush.png' <><><><>"); cv.SaveImage("_Inocolflush.png", I)
        x1_left = find_col_x1(I, Icol, bb_left)
        x1_right = find_col_x1(I, Icol, bb_right)
        print_dbg("== x1_left={0} x1_right={1}".format(x1_left, x1_right))
        x1_left = x1_left if x1_left != None else 0
        x1_right = (min(h-1, x1_right+w_markfull) if x1_right != None else w-1)
    else:
        x1_left, x1_right = 0, w-1
    bb_thecols = (x1_left, 0, x1_right, h-1)
    shift_roi(I, bb_thecols[0], bb_thecols[1], bb_thecols[2] - bb_thecols[0], bb_thecols[3] - bb_thecols[1])
    roi_flushcol = cv.GetImageROI(I)
    if DEBUG_SAVEIMGS:
        print_dbg("<><><><> Saving '_Iflushcols.png' <><><><>"); cv.SaveImage("_Iflushcols.png", I)
        pdb.set_trace()
    for bb_rough in bbs_rough:
        cv.SetImageROI(I, roi_flushcol)
        shift_roi(I, bb_rough[0], bb_rough[1], bb_rough[2] - bb_rough[0], bb_rough[3] - bb_rough[1])
        w_foo, h_foo = cv.GetSize(I)
        Icor, H = rotate_img(I, -theta)

        Hfoo = np.eye(3)
        Hfoo[0:2, 0:3] = np.array(H)
        H_inv = np.linalg.inv(Hfoo)
        H_inv = H_inv[0:2]

        if DEBUG_SAVEIMGS:
            print_dbg("<><><><> Saving '_Icor.png' <><><><>")
            cv.SaveImage("_Icor.png", Icor)
        i1_blk_cor, i2_blk_cor, j1_blk_cor, j2_blk_cor = compute_border(iplimage2np(Icor))
        shift_roi(Icor, j1_blk_cor, i1_blk_cor, cv.GetSize(Icor)[0]-(j1_blk_cor+j2_blk_cor), cv.GetSize(Icor)[1]-(i1_blk_cor+i2_blk_cor))

        if DEBUG_SAVEIMGS:
            print_dbg("<><><><> Saving '_Icor_noblkborder.png' <><><><>")
            cv.SaveImage("_Icor_noblkborder.png", Icor)

        def to_orig_coords(bb, H_inv):
            """ Returns BB (in corrected coord. system) to the original
            coordinate system.
            """
            x1, y1 = transform_pt((bb[0], bb[1]), H_inv, (w_foo, h_foo))
            x1 += bb_rough[0] + bb_thecols[0]
            y1 += bb_rough[1]
            x2, y2 = transform_pt((bb[2], bb[3]), H_inv, (w_foo, h_foo))
            x2 += bb_rough[0] + bb_thecols[0]
            y2 += bb_rough[1]
            return tuple(map(lambda x: int(round(x)), (x1,y1,x2,y2)))

        w_cor, h_cor = cv.GetSize(Icor)
        candidates = []
        y1_step = int(h_markfull / 4.0)
        def tighten_bbs(bbs, decoding, I):
            """ Given initial boundingboxes around each mark, compute
            new bbs such that each 'on' mark is at the upper-left corner.
            """
            def find_black(I, x, BLACK=130, y1_start=0):
                """ Find y1 of first black pixel, starting from (X, 0). """
                w, h = cv.GetSize(I)
                for y1 in xrange(y1_start, h):
                    if I[y1,x] <= BLACK:
                        return y1
                return None
            w_img, h_img = cv.GetSize(I)
            bbs_out = []
            y1s_ons = []
            if DEBUG_SAVEIMGS:
                print_dbg("<><><><> Saving '_Itightenbbs.png' <><><><>")
                cv.SaveImage("_Itightenbbs.png", I)
            # First, estimate the y1's for the left/right col marks,
            # since they're the 'easiest' to find
            y1s_leftright = []
            for (x1,y1,x2,y2) in (bbs[0], bbs[-1]):
                w_rect, h_rect = (x2-x1), (y2-y1)
                x1s = (x1+int(w_rect*0.15), x1+int(w_rect/4.0), x1+int(w_rect/2.0), x1+int((3*w_rect)/4.0), (x2-1)-int(w_rect*0.1))
                x1s = [x for x in x1s if x < w_img]
                y1s = [find_black(I, x1_cur, y1_start=0) for x1_cur in x1s]
                y1s = [_y1 for _y1 in y1s if _y1 != None]
                if not y1s:
                    y1_out = 0 # Default to sensible value
                else:
                    y1_out = int(round(np.median(y1s)))
                y1s_leftright.append(y1_out)

            for i, (x1,y1,x2,y2) in enumerate(bbs):
                val = decoding[i]
                if val == '0':
                    bbs_out.append((x1,y1,x2,y2))
                    continue
                w_rect, h_rect = (x2-x1), (y2-y1)
                x1s = (x1+int(w_rect*0.15), x1+int(w_rect/4.0), x1+int(w_rect/2.0), x1+int((3*w_rect)/4.0), (x2-1)-int(w_rect*0.1))
                x1s = [x for x in x1s if x < w_img]
                if i == 0 or i == len(bbs)-1:
                    _y1 = 0
                else:
                    _y1 = max(int(round(y1 - (h_markfull / 4.0))), 0)

                y1s = [find_black(I, x1_cur, y1_start=_y1) for x1_cur in x1s]
                y1s = [_y1 for _y1 in y1s if _y1 != None] # Filter out the bad results
            
                #y1_out = int(round((np.mean(y1s)+np.median(y1s))/2.0))
                if not y1s:
                    y1_out = 0 # Default to sensible value
                else:
                    y1_out = int(round(np.median(y1s)))
                y2_out = y1_out + (y2-y1) - 1
                y1s_ons.append(y1_out)
                bbs_out.append((x1, y1_out-1, x2, y2_out-1))
            # Finally, clamp all y1s of '0' marks to some fixed y1
            y1_clamp = int(round(np.mean(y1s_ons)))
            bbs_out_final = []
            for i, (x1,y1,x2,y2) in enumerate(bbs_out):
                if decoding[i] == '0':
                    bbs_out_final.append((x1,y1_clamp,x2,y1_clamp+(y2-y1)-1))
                else:
                    bbs_out_final.append((x1,y1,x2,y2))
            return bbs_out_final

        for step in xrange(int((h_cor-1) / y1_step)):
            if step == 0:
                shift_roi(Icor, 0, 0, w_cor, h_markfull)
            else:
                # Don't shift down on first iteration!
                shift_roi(Icor, 0, y1_step, w_cor, h_markfull)
            if DEBUG_SAVEIMGS:
                print_dbg("<><><><> Saving '_Icor_strip.ong' <><><><>")
                cv.SaveImage("_Icor_strip.png", Icor)
                pdb.set_trace()

            # list SYMS := [(str VAL, int X1), ...]
            syms, params_ = scan_bars.parse_patch(Icor, (w_markfull, h_markfull), gap=H_GAP, 
                                                  LEN=34,
                                                  orient=scan_bars.HORIZONTAL, MARKTOL=0.7,
                                                  BEGIN_TOL=0.3, END_TOL=0.3,
                                                  GAMMA=0.7,
                                                  idx2tol=idx2tol)
            decoding = ''.join([t[0] for t in syms])
            pix_on, pix_off = params_["pix_on"], params_["pix_off"]
            def is_pixon_pixoff_ok():
                if PIX_ON_OFF_RATIO != None:
                    return (pix_on / pix_off) < PIX_ON_OFF_RATIO
                else:
                    return True

            if not sanitycheck_decoding_v2(decoding) or (not is_pixon_pixoff_ok()):
                print_dbg("(SanityCheck) FAIL -- '{0}' ({1})".format(decoding, len(decoding)))
                continue

            if EXP_PARAMS:
                global GLOB_PARAMS_
                if GLOB_PARAMS_ == None:
                    GLOB_PARAMS_ = {"PIX_ON": [], "PIX_OFF": []}
                GLOB_PARAMS_["PIX_ON"].append(params_['pix_on'])
                GLOB_PARAMS_["PIX_OFF"].append(params_['pix_off'])
                
            markbbs_rough = [(t[1], 0, t[1]+W_MARK, H_MARK-1) for t in syms]
            # Find a tighter y1 for the black marks
            bbs = tighten_bbs(markbbs_rough, decoding, Icor)
            # Correct for current-offset in sweep
            #bbs_out = [(t[1], y1_step*step, t[1] + w_markfull, y1_step*step + h_markfull) for t in syms]
            bbs_out = [(t[0], t[1]+(y1_step*step), t[2], t[3]+(y1_step*step)) for t in bbs]
            # Undo rotation correction
            bbs_out = [to_orig_coords(bb, H_inv) for bb in bbs_out]
            # Add the compute_border offsets (part1)
            bbs_out = [(x1+j1_blk_cor, y1+i1_blk_cor, x2+j1_blk_cor, y2+i1_blk_cor) for (x1,y1,x2,y2) in bbs_out]            
            # Add the compute_border offsets
            #bbs_out = [(x1+j1_blk, y1+i1_blk, x2+j1_blk, y2+i2_blk) for (x1,y1,x2,y2) in bbs_out]
            bbs_out = [(x1+j1_blk, y1+i1_blk, (x1+W_MARK-1)+j1_blk, (y1+H_MARK-1)+i1_blk) for (x1,y1,x2,y2) in bbs_out]
            if DEBUG_SAVEIMGS:
                print_dbg("==== decoding ({0}): {1}".format(len(decoding), decoding))
                Icolor = draw_bbs(imgpath, decoding, bbs_out, isflip)
                cv.SaveImage("_dbg_showit.png", Icolor)
                print "<><><><> Saving '_dbg_showit.png' <><><><>"
                dbg_bbs_out = [(t[1], y1_step*step, t[1] + w_markfull, y1_step*step + h_markfull) for t in syms]
                # Undo rotation correction
                dbg_bbs_out = [to_orig_coords(bb, H_inv) for bb in dbg_bbs_out]
                # Add the compute_border offsets (part1)
                dbg_bbs_out = [(x1+j1_blk_cor, y1+i1_blk_cor, x2+j1_blk_cor, y2+i2_blk_cor) for (x1,y1,x2,y2) in dbg_bbs_out]
                # Add the compute_border offsets
                dbg_bbs_out = [(x1+j1_blk, y1+i1_blk, x2+j1_blk, y2+i2_blk) for (x1,y1,x2,y2) in dbg_bbs_out]
                Icolor_notighten = draw_bbs(imgpath, decoding, dbg_bbs_out, isflip)
                cv.SaveImage("_dbg_showit_notighten.png", Icolor_notighten)
                print "<><><><> Saving '_dbg_showit_notighten.png' <><><><>"
                pdb.set_trace()

            if sanitycheck_decoding_v2(decoding):
                candidates.append((decoding, isflip, bbs_out))
        if candidates:
            result = most_popular(candidates, W_MARK=W_MARK, H_MARK=H_MARK)
        if result != None:
            break
        print_dbg("==== Trying another bb_rough")
    cv.SetImageROI(I, roi_prev)
    return result

def most_popular(candidates, W_MARK=WIDTH_MARK, H_MARK=HEIGHT_MARK):
    """ Returns the most-common decoding possibilty (recall that this
    decoder may output multiple, possibly-different decodings).
    """
    votes = {}
    outputs = {} # maps {str decoding: [(isflip_i, bbs_i), ...]}
    for decoding, isflip, bbs_out in candidates:
        outputs.setdefault(decoding, []).append((isflip, bbs_out))
        if decoding not in votes:
            votes[decoding] = 1
        else:
            votes[decoding] += 1
    best_decoding, best_isflip, best_bbs_out, best_votes = None, None, None, None
    for decoding, vote_cnt in votes.iteritems():
        if best_decoding == None or vote_cnt > best_votes:
            best_decoding = decoding
            best_votes = vote_cnt
    best_outputs = outputs[best_decoding] # [(isflip_i, bbs_i), ...]
    def extrapolate_bbs(bbs_lst, fn=np.median):
        """ Determine 'best' bbs for each mark. """
        if len(bbs_lst) == 1:
            return bbs_lst[0]
        bbs_out = []
        for i in xrange(len(bbs_lst[0])):
            x1s, y1s, x2s, y2s = [], [], [], []
            for bbs in bbs_lst:
                bb = bbs[i]
                x1s.append(bb[0])
                y1s.append(bb[1])
                x2s.append(bb[2])
                y2s.append(bb[3])
            x1 = int(round(fn(x1s)))
            y1 = int(round(fn(y1s)))
            x2 = x1 + W_MARK - 1
            y2 = y1 + H_MARK - 1
            #x2 = int(round(fn(x2s)))
            #y2 = int(round(fn(y2s)))
            bbs_out.append((x1,y1,x2,y2))
        return bbs_out
        
    best_isflip = best_outputs[0][0]
    best_bbs_out = extrapolate_bbs([t[1] for t in best_outputs], fn=np.median)
    #best_isflip, best_bbs_out = best_outputs[int(len(best_outputs)/2.0)]
    return best_decoding, best_isflip, best_bbs_out

def sanitycheck_decoding_v2(decoding):
    ALL_ONES = '1'*34
    is_good = True
    # Side-agnostic checks
    is_good = (decoding and len(decoding) == 34 and
               decoding != ALL_ONES)
    dec = decoding[1:-1]
    # Side-specific checks
    if get_page(dec) == 0:
        is_good = is_good and (get_startbit(dec) == '1' and
                               get_seqnum(dec) == '00' and
                               verify_checksum(dec))
    else:
        is_good = is_good and (get_endercode(dec) == '01111011110')
    return is_good

def estimate_ballot_rot(I, Imarkfull, bbs, MAX_THETA=2.0, K=5):
    roi_prev = cv.GetImageROI(I)
    w_markfull, h_markfull = cv.GetSize(Imarkfull)
    theta_tm = None
    for bb in bbs:
        roi_cur = tuple(map(lambda x: int(round(x)),
                            (roi_prev[0] + bb[0], 
                             roi_prev[1] + bb[1],
                             bb[2] - bb[0],
                             bb[3] - bb[1])))
        cv.SetImageROI(I, roi_cur)
        w_cur, h_cur = cv.GetSize(I)

        if DEBUG_SAVEIMGS:
            print_dbg("<><><><> Saving '_Imiddle.png' <><><><>")
            cv.SaveImage("_Imiddle.png", I)
            pdb.set_trace()

        matches = tempmatch.get_tempmatches(Imarkfull, [I], T=0.9, do_smooth=tempmatch.SMOOTH_BOTH_BRD,
                                            xwinI=5, ywinI=5, xwinA=5, ywinA=5)[0]
        matches = sorted(matches, key=lambda t: t[0])
        if matches:
            xs = np.array([t[0] for t in matches])
            ys = np.array([cv.GetSize(I)[1] - t[1] for t in matches])
            if len(xs) <= 1:
                print_dbg("==== Couldn't find enough marks in '_Imiddle.png'.")
                continue
            # Filter out any obvious outliers
            lonely_idxs = detect_lonely_vals(ys, h_markfull)
            xs = np.delete(xs, lonely_idxs)
            ys = np.delete(ys, lonely_idxs)
            if len(xs) <= 1:
                print_dbg("==== Couldn't find enough marks in '_Imiddle.png'.")
                continue
            # Discovered marks must take up at least K*w_markfull space.
            x_area = max(xs) - min(xs)
            if x_area < (K * w_markfull):
                print_dbg("==== Marks only took up {0}, too small space.".format(x_area))
            else:
                theta_tm_ = estimate_rotation(xs, ys)
                if abs(theta_tm_) > MAX_THETA:
                    print_dbg("==== Theta was too large: {0}".format(theta_tm_))
                else:
                    theta_tm = theta_tm_
                    break
        else:
            print_dbg("==== Couldn't find any marks in '_Imiddle.png'.")

    cv.SetImageROI(I, roi_prev)

    return theta_tm

def detect_lonely_vals(vals, h_mark, C=2.0):
    """ Detect values V which doesn't have a different value V' within
    the neighborhood [V - (h_mark*C), V + (h_mark*C)].
    """
    i = 0
    lonely_idxs = []
    while i < len(vals):
        has_friend = False
        val_i = vals[i]
        j = 0
        while j < len(vals):
            if i == j:
                j += 1
                continue
            val_j = vals[j]
            if abs(val_i - val_j) <= (h_mark * C):
                has_friend = True
                break
            j += 1
        if not has_friend:
            lonely_idxs.append(i)
        i += 1
    return lonely_idxs

def transform_pt(pt, H0, Isize):
    x,y = pt
    w, h = Isize
    H = np.eye(3)
    H[0:2, 0:3] = np.array(H0)
    out = np.dot(H, [x,y,1])
    return int(round(out[0])), int(round(out[1]))

def get_rotmat(I, degrees):
    w, h = cv.GetSize(I)
    rotmat = cv.CreateMat(2, 3, cv.CV_32F)
    cv.GetRotationMatrix2D((w/2, h/2), degrees, 1.0, rotmat)
    return rotmat
def apply_rot(I, H):
    Idst = cv.CreateImage(cv.GetSize(I), I.depth, I.channels)
    cv.WarpAffine(I, Idst, H, fillval=255.0)
    return Idst
def rotate_img(I, degrees):
    H = get_rotmat(I, degrees)
    Idst = apply_rot(I, H)
    return Idst, H

def shift_roi(I, x, y, w, h):
    roi_prev = cv.GetImageROI(I)
    new_roi = tuple(map(int, 
                        (roi_prev[0] + x, roi_prev[1] + y, w, h)))
    cv.SetImageROI(I, new_roi)
    return I

def drawit(I, bbs, imgpath, isflip=False):
    Icolor = cv.LoadImage(imgpath, cv.CV_LOAD_IMAGE_COLOR)
    if isflip:
        cv.Flip(Icolor, Icolor, -1)
    cv.SetImageROI(Icolor, cv.GetImageROI(I))
    for (x1,y1,x2,y2) in bbs:
        cv.Rectangle(Icolor, (x1,y1), (x2,y2), cv.CV_RGB(255, 0, 0))
    print "<><><><> Saving '_Icolor.png' <><><><>"
    cv.SaveImage("_Icolor.png", Icolor)
    pdb.set_trace()

def estimate_rotation(xs, ys):
    # Assumption: len(xs) >= 2
    if not np.any(ys != ys[0]):
        # All the same YS - explicitly return 0.0 to avoid linregress error
        return 0.0
    elif len(xs) == 2:
        # scipy.stats.linregress errors on two points. 
        slope = (ys[1] - ys[0]) / float(xs[1] - xs[0])
        return math.degrees(math.atan2(slope, 1.0))
    slope, intercept, rval, pval, std_err = scipy.stats.linregress(xs, ys)
    degrees = math.degrees(math.atan2((slope*1.0 + intercept) - intercept, 1.0 - 0.0))
    return degrees

"""
==========================================================
==== Diebold-specific barcode interpretation routines ====
==========================================================
"""
""" Information about Front side barcode """
def get_checksum(decoding):
    return decoding[30:32]
def get_precinct(decoding):
    return decoding[17:30]
def get_cardnum(decoding):
    return decoding[4:17]
def get_seqnum(decoding):
    return decoding[1:3]
def get_startbit(decoding):
    return decoding[0]

""" Information about Back side barcode """
def get_day(decoding):
    return decoding[27:32]
def get_month(decoding):
    return decoding[23:27]
def get_year(decoding):
    return decoding[16:23]
def get_electiontype(decoding):
    return decoding[11:16]
def get_endercode(decoding):
    return decoding[0:11]

def get_page(decoding):
    """ Back side always ends with 01111011110. Outputs an int: 0/1. """
    return 0 if not get_endercode(decoding) == '01111011110' else 1

def compute_checksum(decoding):
    """ To compute a Diebold-style checksum, take the number of '1' bits
    in bits 2-31, reduced modulo 4.
    """
    return len([v for v in decoding[:-2] if v == '1']) % 4
def verify_checksum(decoding):
    chksum_a = compute_checksum(decoding)

    b = get_checksum(decoding)
    chksum_b = 2*int(b[0]) + int(b[1])
    return chksum_a == chksum_b

""" END Diebold barcode interpretation routines """

def isimgext(f):
    return os.path.splitext(f)[1].lower() in ('.png', '.jpg', '.jpeg', '.bmp')

def draw_bbs(imgpath, decoding, bbs, isflip=False):
    Icolor = cv.LoadImage(imgpath, cv.CV_LOAD_IMAGE_COLOR)
    if isflip:
        cv.Flip(Icolor, Icolor, -1)
    for i, (x1,y1,x2,y2) in enumerate(bbs):
        color = cv.CV_RGB(255, 0, 0) if decoding[i] == '0' else cv.CV_RGB(0, 0, 255)
        cv.Rectangle(Icolor, (x1,y1), (x2,y2), color, thickness=2)
    return Icolor

def rescale_img(I, c):
    """ Scales image I by factor C. For instance, to upscale an image
    by a factor of 2, pass in c=2.0. """
    if c == 1.0:
        return cv.CloneImage(I)
    w_cur, h_cur = cv.GetSize(I)
    w_new, h_new = int(round(w_cur * float(c))), int(round(h_cur * float(c)))
    Iout = cv.CreateImage((w_new, h_new), I.depth, I.channels)
    if c > 1.0:
        # Downsizing
        cv.Resize(I, Iout, interpolation=cv.CV_INTER_AREA)
    else:
        cv.Resize(I, Iout, interpolation=cv.CV_INTER_CUBIC)
    return Iout

def plot_params(all_params):
    """
    Input:
        dict ALL_PARAMS: {'PIX_ON': [float p, ...], 'PIX_OFF': [float p, ...]}
    """
    fig = plt.figure()
    p_on = fig.add_subplot(211)
    p_off = fig.add_subplot(212)
    
    pix_ons = all_params['PIX_ON']
    pix_offs = all_params["PIX_OFF"]

    print "pix_ons  MEAN := {0}".format(np.mean(pix_ons))
    print "pix_ons  STD  := {0}".format(np.std(pix_ons))
    print "pix_offs MEAN := {0}".format(np.mean(pix_offs))
    print "pix_offs STD  := {0}".format(np.std(pix_offs))

    ons_hist, ons_bins = np.histogram(pix_ons)
    offs_hist, offs_bins = np.histogram(pix_offs)
    
    def plot_hist(hist, bins, plt):
        width = 0.7*(bins[1]-bins[0])
        center = (bins[:-1]+bins[1:])/2
        plt.bar(center, hist, align = 'center', width = width)

    plot_hist(ons_hist, ons_bins, p_on)
    plot_hist(offs_hist, offs_bins, p_off)

    fig.savefig("ons_and_offs.png")

    fig_ratios = plt.figure()
    p_ratios = fig_ratios.add_subplot(111)

    ratios = [float(pix_on / pix_offs[i]) for i, pix_on in enumerate(pix_ons)]

    print "ratios MEAN := {0}".format(np.mean(ratios))
    print "ratios STD  := {0}".format(np.std(ratios))

    rat_hist, rat_bins = np.histogram(ratios)
    
    plot_hist(rat_hist, rat_bins, p_ratios)
    
    fig_ratios.savefig("ons_and_offs_ratios.png")

def main():
    args = sys.argv[1:]
    arg0 = args[-1]
    do_show = '--show' in args
    do_compare = '--compare' in args
    try: N = int(args[args.index('-n')+1])
    except: N = None
    try: outpath = args[args.index('-o')+1]
    except: outpath = None
    try: erroutpath = args[args.index('--erroutpath')+1]
    except: erroutpath = 'errs_diebold_raw.txt'
    try: true_results = pickle.load(open(args[args.index('--compare')+1], 'rb'))
    except: true_results = None

    global DEBUG, DEBUG_SAVEIMGS, DEBUG_SKIP_FLIP, EXP_PARAMS
    DEBUG = '--debug' in args
    DEBUG_SAVEIMGS = '--saveimgs' in args
    DEBUG_SKIP_FLIP = '--skipflip' in args
    EXP_PARAMS = '--exp_params' in args
    
    if isimgext(arg0):
        imgpaths = [arg0]
    elif os.path.isdir(arg0):
        imgpaths = []
        for dirpath, dirnames, filenames in os.walk(arg0):
            for imgname in [f for f in filenames if isimgext(f)]:
                imgpaths.append(os.path.join(dirpath, imgname))
    else:
        # is file containing image paths on each line
        imgpaths = [line.strip() for line in open(arg0).readlines() if line]

    t = time.time()
    cnt = 0
    decoding2imgs = {} # maps {str decoding: [imgpath_i, ...]}
    img2decoding = {} # maps {imgpath: str decoding}
    flipmap = {} # maps {str imgpath: bool isflip}
    img2bbs = {} # maps {str imgpath: [bb_i, ...]}
    errs = []
    Imarkfull = cv.LoadImage(MARKFULL_PATH, cv.CV_LOAD_IMAGE_GRAYSCALE)
    Icol = cv.LoadImage(COLMARK_PATH, cv.CV_LOAD_IMAGE_GRAYSCALE)
    w_cur, h_cur = cv.GetSize(cv.LoadImage(imgpaths[0], cv.CV_LOAD_IMAGE_UNCHANGED))
    W_ORIG, H_ORIG = SIZE_ORIG
    h_gap_cur = HORIZ_GAP
    w_mark, h_mark = WIDTH_MARK, HEIGHT_MARK
    if w_cur != W_ORIG or h_cur != H_ORIG:
        c = w_cur / float(W_ORIG)
        print "...Detected current image resolution {0} differs from \
original resolution {1}. Rescaling Imark, Icol, H_GAP accordingly...".format((w_cur, h_cur),
                                                                             (W_ORIG, H_ORIG))
        Imarkfull = rescale_img(Imarkfull, c)
        Icol = rescale_img(Icol, c)
        h_gap_cur = int(round(HORIZ_GAP * c))
        w_mark = int(round(WIDTH_MARK * c))
        h_mark = int(round(HEIGHT_MARK * c))
        
    for imgpath in imgpaths:
        if N != None and cnt >= N:
            break
        try:
            decoding, isflip, bbs = decode_robust_v2(imgpath, Imarkfull, Icol, H_GAP=h_gap_cur,
                                                     W_MARK=w_mark, H_MARK=h_mark)
        except Exception as e:
            if type(e) == KeyboardInterrupt:
                raise e
            traceback.print_exc()
            decoding = None

        if decoding == None:
            print 'Error:', imgpath
            errs.append(imgpath)
            if do_show:
                cv.SaveImage("_showit_fail.png", cv.LoadImage(imgpath))
                print "<><><><> Saved '_showit_fail.png' <><><><>"
                pdb.set_trace()
        else:
            print "{0}: {1} ({2})".format(os.path.split(imgpath)[1], decoding, len(decoding))
            print "    isflip={0}  {1}".format(isflip, imgpath)
            if do_show:
                Icolor = draw_bbs(imgpath, decoding, bbs, isflip=isflip)
                cv.SaveImage("_showit.png", Icolor)
                print "<><><><> Saved '_showit.png' <><><><>"
                pdb.set_trace()
            decoding2imgs.setdefault(decoding, []).append(imgpath)
            img2decoding[imgpath] = decoding
            flipmap[imgpath] = isflip
            img2bbs[imgpath] = bbs
        cnt += 1

    total_dur = time.time() - t
    print "...Done ({0:.6f} s).".format(total_dur)
    if N == None:
        print "    Average Time Per Image: {0:.6f} s".format(total_dur / float(len(imgpaths)))
    else:
        print "    Average Time Per Image: {0:.6f} s".format(total_dur / float(N))
    print "    Number of Errors: {0}".format(len(errs))

    if EXP_PARAMS:
        plot_params(GLOB_PARAMS_)

    if do_compare:
        are_inconsistensies = False
        true_decoding2imgs, true_img2decoding, true_flipmap, true_img2bbs, true_errs = true_results
        wrong_map = compare_decodings(decoding2imgs, img2decoding, true_decoding2imgs, true_img2decoding)
        num_wrongs = len(wrong_map)
        for imgpath, (our_dec, true_dec) in wrong_map.iteritems():
            print "For imgpath={0}:".format(imgpath)
            print "    Our Decoding:", our_dec
            print "   True Decoding:", true_dec
        print "==== Number of Inconsistensies:", num_wrongs
        if num_wrongs > 0:
            are_inconsistensies = True
    else:
        are_inconsistensies = False

    if outpath:
        outfile = open(outpath, 'wb')
        if are_inconsistensies:
            response = raw_input("Inconsistensies were detected. Are you \
sure you want to dump to {0}? (y/n)".format(outpath))
            if response and response.strip().lower() in ('y', 'yes'):
                pickle.dump((decoding2imgs, img2decoding, flipmap, img2bbs, errs), outfile)
                print "...Saved pickle'd files to: {0}...".format(outpath)
        else:
            pickle.dump((decoding2imgs, img2decoding, flipmap, img2bbs, errs), outfile)
            print "...Saved pickle'd files to: {0}...".format(outpath)

    if errs:
        do_write = raw_input("Would you like to write out all err imgpaths to '{0}' (Y/N)?".format(erroutpath))
        if do_write and do_write.strip().lower() in ('y', 'yes'):
            print "...Writing all err imgpaths to '{0}'...".format(erroutpath)
            f = open(erroutpath, 'w')
            for errpath in errs:
                print >>f, errpath

    print "Done."

def compare_decodings(dec2imgs, img2dec, true_dec2imgs, true_img2dec):
    wrong_map = {} # maps {str imgpath: [str our_answer, str true_answer]}
    for true_decoding, imgpaths in true_dec2imgs.iteritems():
        for imgpath in imgpaths:
            our_decoding = img2dec.get(imgpath, None)
            if our_decoding != true_decoding:
                wrong_map[imgpath] = [our_decoding, true_decoding]
        
    return wrong_map

if __name__ == '__main__':
    main()
