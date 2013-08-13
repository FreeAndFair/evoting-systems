import sys, time, pdb, argparse
import numpy as np
import cv

TOP_GUARD_IMGP = 'hart_topguard.png'
BOT_GUARD_IMGP = 'hart_botguard.png'

TOP_GUARD_SKINNY_IMGP = 'hart_topguard_skinny.png'
BOT_GUARD_SKINNY_IMGP = 'hart_botguard_skinny.png'

BC_14_IMGP = 'hart_bc_14.png'
BC_12_IMGP = 'hart_bc_12.png'
BC_10_IMGP = 'hart_bc_10.png'

BC_14_HEIGHT = 489
BC_12_HEIGHT = 450

VERTICAL = 1
HORIZONTAL = 2
WIDE = 'W'
NARROW = 'N'

WHITE_WIDE = 'whiteWide'
WHITE_NARROW = 'whiteNarrow'
BLACK_WIDE = 'blackWide'
BLACK_NARROW = 'blackNarrow'

def decode_i2of5(img, n, topbot_pairs, orient=VERTICAL, debug=False, 
                 imgP=None, cols=4):
    """ Decodes the interleaved two-of-five barcode. Returns a string.
    Input:
        IplImage img:
        int n: Number of digits in the barcode.
        list TOPBOT_PAIRS: [[IplImage topguard, IplImage botguard], ...]. 
        int COLS: Splits the barcode into COLS columns, separately
            runs the decoding on each column, then chooses the most
            popular decoding result.
    Output:
        (str decoded, tuple bb), where BB is the bounding box of the
        barcode within IMG: (x, y, w, h)
    """
    # For now, assume that the barcode is bottom-to-top.
    TOP_GUARD, BOT_GUARD = topbot_pairs[0]

    TOP_GUARD = smooth_constborder(TOP_GUARD, xwin=3, ywin=3, val=255)
    BOT_GUARD = smooth_constborder(BOT_GUARD, xwin=3, ywin=3, val=255)

    TOP_WHITE_PAD = 24  # Num. pixs from white->top guard barcode
    BOT_WHITE_PAD = 31
    
    # 1.) Find location of top/bottom guards, to find location of barcode
    bc_height = BC_14_HEIGHT if n == 14 else BC_12_HEIGHT
    bc_loc = find_barcode_loc_tm(img, bc_height, TOP_GUARD, BOT_GUARD, 
                                 TOP_WHITE_PAD, BOT_WHITE_PAD, imgP=imgP)
    if bc_loc == None:
        if len(topbot_pairs) == 1:
            return None, [0, 0, 1, 1], None
        return decode_i2of5(img, n, topbot_pairs[1:], imgP=imgP, cols=cols, debug=debug)

    # 2.) Crop the barcode.
    #cv.SaveImage("_imgcrop_pre.png", img)
    roi_precrop = cv.GetImageROI(img)
    cv.SetImageROI(img, shiftROI(cv.GetImageROI(img),
                                 bc_loc))
    #cv.SaveImage("_imgcrop.png", img)
    decodings = []
    w_bc, h_bc = cv.GetSize(img)
    bc_roi = cv.GetImageROI(img)
    for curcol in xrange(cols):
        width = int(round(w_bc / cols))
        x1 = width * curcol
        cv.SetImageROI(img, shiftROI(bc_roi, (x1, 0, width, h_bc)))
        decodings.append(decode_barcode(img, n, bc_loc[:], xoff=x1, imgP=imgP, debug=debug))

    dstr_out, bbloc_out, bbstripes_out = get_most_popular(decodings, w_bc)
    cv.SetImageROI(img, roi_precrop)

    if dstr_out == None:
        if len(topbot_pairs) == 1:
            # We tried our best, give up.
            return dstr_out, bbloc_out, bbstripes_out
        else:
            return decode_i2of5(img, n, topbot_pairs[1:],
                                imgP=imgP, cols=cols, debug=debug)
    return dstr_out, bbloc_out, bbstripes_out

def get_most_popular(decodings, w_bc):
    decoding = None
    votes = {} # maps {decoded_str: int count}
    othermap = {} # maps {decoded_str: bc_loc}
    none_bc_loc = None
    for decoded_str, bc_loc, bbstripes in decodings:
        bc_loc = tuple(bc_loc)
        if decoded_str == None:
            if bc_loc != None:
                none_bc_loc = bc_loc
            continue
        if decoded_str not in votes:
            votes[decoded_str] = 1
            othermap[decoded_str] = [(bc_loc, bbstripes)]
        else:
            votes[decoded_str] += 1
            othermap[decoded_str].append((bc_loc, bbstripes))
    if votes:
        best_decodedstr = sorted(votes.items(), key=lambda t:t[1])[0][0]
        tuples = othermap[best_decodedstr]
        # BEST_BBSTRIPES: maps {stripeType: [[x1,y1,w,h], ...]}
        best_bcloc, best_bbstripes = tuples[int(len(tuples) / 2)]
        # Correct the BB stripes to encompass the entire width of barcode
        bbstripes_out = {} 
        for stripetype, bbs in best_bbstripes.iteritems():
            newbbs = [(0, y1, w_bc, h) for (x1,y1,w,h) in bbs]
            bbstripes_out[stripetype] = newbbs
        return best_decodedstr, best_bcloc, bbstripes_out
    return None, none_bc_loc, None
        
def decode_barcode(img, n, bc_loc, xoff=0, debug=False, imgP=None):
    """ Given an image patch IMG that is a tight-bounding box around the 
    barcode, return the decoding.
    Input:
        IplImage IMG
        int N: Number of digits in barcode
        tuple BC_LOC: [x1,y1,w,h], location of the entire barcode.
        int XOFF: X offset into the current barcode. Used to correct
            the x1 for BBSTRIPES_OUT.
    Output:
        (str DECODING, list BB, dict BBSTRIPES_OUT)
    """
    img_post = dothreshold(img)
    #cv.SaveImage("_imgpost.png", img_post)
    #img_post = img
    w_imgpost, h_imgpost = cv.GetSize(img_post)

    # dict BBSTRIPES: maps {'whiteNarrow': [[x1,y1,w,h], ...], 'whiteWide': [[x1,y1,w,h], ...],
    #                       'blackNarrow': ..., 'blackWide': ...}
    bbstripes = {}

    # 3.) Collapse the barcode to be 1D (by summing pix intensity values
    # to the parallel axis). 
    flat = cv.CreateMat(h_imgpost, 1, cv.CV_32S)
    cv.Reduce(img_post, flat, dim=1, op=cv.CV_REDUCE_SUM)
    flat_np = np.asarray(flat)[::-1][:,0]
    flat_tpl = tuple(flat_np)

    # 4.) Now we have something like [100 100 100 0 0 0 100 100 100 0 0 0 ...].
    # Compute the PIX_ON/PIX_OFF, which tells us what intensity
    # value is 'black' or 'white' by computing the histogram of FLAT.
    pix_on, pix_off = infer_on_off(flat_np)
    #print 'pix_on, pix_off:', pix_on, pix_off
    # 4.a.) Advance to start of barcode
    i, foundbegin = 0, False
    while i < len(flat_tpl) and not foundbegin:
        val = flat_tpl[i]
        if is_pix_on(val, pix_on, pix_off):
            foundbegin = True
        else:
            i += 1
    if not foundbegin: 
        print "Uhoh, couldn't find start of barcode?"
        if debug:
            pdb.set_trace()
        return None, bc_loc, None
    start_idx = i
    bc_loc[3] -= i    # skip to start of barcode

    # 4.b.) Find W_NARROW, W_WIDE, B_NARROW, B_WIDE
    # Due to image artifacts, wide/narrow may differ for black/white.
    w_narrow, w_wide = 0.0, 0.0
    b_narrow, b_wide = 0.0, 0.0

    whts, blks = [], []
    curlen = 0
    isblack = is_pix_on(flat_np[start_idx], pix_on, pix_off)
    UPPER_LIMIT = n * 5 + 7 # Number of stripes, including (7) for top/bot guards
    # stores y1-idxs of all detected stripes
    whts_ys, blks_ys = [], []
    for idx, val in enumerate(flat_tpl[start_idx:]):
        if (len(whts) + len(blks)) >= UPPER_LIMIT:
            break
        if is_pix_on(val, pix_on, pix_off):
            if not isblack:
                # Entering Black
                whts_ys.append(h_imgpost - (idx+start_idx-1) - 1)
                whts.append(curlen)
                curlen = 1
            else:
                curlen += 1
            isblack = True
        elif not is_pix_on(val, pix_on, pix_off):
            if isblack:
                # Entering White
                blks_ys.append(h_imgpost - (idx+start_idx-1) - 1)
                blks.append(curlen)
                curlen = 1
            else:
                curlen += 1
            isblack = False
        else:
            curlen += 1

    if (len(whts) + len(blks) < UPPER_LIMIT) and curlen > 1:
        # Add the upper-most black stripe, which didn't get added inside the for-loop
        blks_ys.append(h_imgpost - (idx+start_idx-1) - 1)
        blks.append(curlen)
        
    if len(whts) + len(blks) != UPPER_LIMIT:
        return None, bc_loc, None

    w_narrow, w_wide = infer_narrow_wide(whts)
    b_narrow, b_wide = infer_narrow_wide(blks)
    if w_narrow == 0 or w_wide == 0 or b_narrow == 0 or b_wide == 0:
        # Default to sensible values if badness happens. 
        w_narrow = 2.0
        w_wide = 8.0
        b_narrow = 3.0
        b_wide = 10.0
    w_wide = min(w_wide, 12)
    b_wide = min(b_wide, 12)
    
    # 5.) Convert the FLAT_NP to something like [Nblk, Nwht, Wblk, Wwht],
    # i.e. 'Narrow black', 'Wide white'. 
    # 5.b.) Do Convert.
    all_bars_wht = stripes_to_bars(whts, w_narrow, w_wide, imgP=imgP)
    all_bars_blk = stripes_to_bars(blks, b_narrow, b_wide, imgP=imgP)
    results = [] # [(str decoded, tuple bc_loc), ...]
    # 5.c.) Iterate over all possible interpretations from stripes_to_bars
    for bars_wht in all_bars_wht:
        if (bars_wht[0] != NARROW or bars_wht[1] != NARROW):
            print "Warning: WHITE Begin-guard not found."
        bars_wht_noguard = bars_wht[2:-1]
        for bars_blk in all_bars_blk:
            # I2OF5 always starts and ends with (N,N,N,N) and (W,N,N).
            if (bars_blk[0] != NARROW or bars_blk[1] != NARROW):
                if debug:
                    print "Warning: Begin-guard not found. Continuing..."
                    pdb.set_trace()
            if (bars_blk[-2] != WIDE or bars_blk[-1] != NARROW):
                if debug:
                    print "Warning: End-guard not found. Continuing..."
                    pdb.set_trace()
            bars_blk_noguard = bars_blk[2:-2]
            # 6.) Interpret BARS.
            decs_blk = bars_to_symbols(bars_blk_noguard)
            decs_wht = bars_to_symbols(bars_wht_noguard)
            if decs_blk == None or decs_wht == None:
                continue
            decoded = ''.join(sum(map(None, decs_blk, decs_wht), ()))
            if len(decoded) != n:
                continue
            bbstripes = compute_stripe_bbs(whts_ys, blks_ys, bars_wht, bars_blk, w_imgpost, xoff,
                                           w_narrow, w_wide,
                                           b_narrow, b_wide)
            results.append((decoded, bc_loc, bbstripes))
    if not results:
        return None, bc_loc, None
    elif len(results) > 1:
        print "...Wow, {0} possible decodings!".format(len(results))
        return None, bc_loc, None
    else:
        return results[0]

def compute_stripe_bbs(whts_ys, blks_ys, bars_wht, bars_blk, width, xoff,
                       wht_narrow, wht_wide,
                       blk_narrow, blk_wide):
    def helper(ys, bars, width, height_narrow, height_wide, color=None):
        out_narrow, out_wide = [], []
        for i, curbar in enumerate(bars):
            cury = ys[i]
            if curbar == WIDE:
                out_wide.append([xoff, cury, width, height_wide])
            else:
                out_narrow.append([xoff, cury, width, height_narrow])
        return out_narrow, out_wide
    whiteNarrows, whiteWides = helper(whts_ys, bars_wht, width, wht_narrow, wht_wide, 'White')
    blackNarrows, blackWides = helper(blks_ys, bars_blk, width, blk_narrow, blk_wide, 'Black')
    return {WHITE_NARROW: whiteNarrows, WHITE_WIDE: whiteWides,
            BLACK_NARROW: blackNarrows, BLACK_WIDE: blackWides}

def bars_to_symbols(bars, debug=False):
    symbols = []
    for i, bars_sym in enumerate(gen_by_n(bars, 5)):
        sym = get_i2of5_val(bars_sym)
        if sym == None:
            #print "...Invalid symbol:", bars_sym
            if debug:
                pdb.set_trace()
            return None
        symbols.append(sym)
    return symbols

def find_barcode_loc_tm(I, bc_height, TOP_GUARD, BOT_GUARD, 
                        TOP_WHITE_PAD, BOT_WHITE_PAD, imgP=None):
    """
    Input:
        IplImage I: Region where a barcode presumably exists.
        int BC_HEIGHT: Estimated height of the barcode.
    Output:
        list BB. [x1, y1, w, h].
        oc_tough_cases/unknown/329_331_25_232_1.png

    """
    w,h = cv.GetSize(I)
    _ROI = cv.GetImageROI(I)
    cv.SetImageROI(I, (_ROI[0], _ROI[1], w, h/2))
    top_mats = get_tempmatches(TOP_GUARD, I, T=0.86, do_smooth=True, xwin=3, ywin=3, atleastone=True)
    cv.SetImageROI(I, _ROI)
    _ROI = cv.GetImageROI(I)
    cv.SetImageROI(I, (_ROI[0], _ROI[1]+h / 2, w, h / 2))
    bot_mats = get_tempmatches(BOT_GUARD, I, T=0.86, do_smooth=True, xwin=3, ywin=3, atleastone=True)
    cv.SetImageROI(I, _ROI)
    # 1.a.) Get top-most/bottom-most match.
    top_sorted = sorted(top_mats, key=lambda t: t[1])  # (46, 58)
    bot_sorted = sorted(bot_mats, key=lambda t: -t[1]) # (46, 74) => (46, 401)
    if not top_sorted and not bot_sorted:
        if debug:
            print "...couldn't find either TOP/BOT guard..."
        return None
    if top_sorted and bot_sorted:
        besttop, bestbot = top_sorted[0], bot_sorted[0]
        # Check that BESTTOP is actually on top of BESTBOT
        if besttop[1] > bestbot[1]:
            return None
    if top_sorted and not bot_sorted:
        (xtop, ytop, sctop) = top_sorted[0]
        (xbot, ybot, scbot) = xtop, ytop + bc_height, 1.0
    elif bot_sorted and not top_sorted:
        (xbot, ybot, scbot) = bot_sorted[0]
        ybot += h / 2 # Account for cropping done above
        (xtop, ytop, sctop) = xbot, ybot - bc_height, 1.0
    else:
        (xtop, ytop, sctop) = top_sorted[0]
        (xbot, ybot, scbot) = bot_sorted[0]
        ybot += h / 2 # Account for cropping done above
    # 1.b.) Correct for the white-padding from topguard/botguard.
    ytop += TOP_WHITE_PAD
    ybot += (BOT_GUARD.height - BOT_WHITE_PAD)
    # 2.) Try to recover from case where top/bot mat is too high/low.
    if abs((ybot-ytop) - bc_height) >= (0.1 * bc_height):
        # Get the more-confident guard match, and work relative to that one
        if sctop > scbot:
            ybot = ytop + bc_height
        else:
            ytop = ybot - bc_height
    bb = [min(xtop, xbot), 
          ytop,
          TOP_GUARD.width,
          int(abs(ybot - ytop))]
    return bb

def infer_on_off(flat_np):
    """ Infers the pix_on/pix_off values from FLAT_NP. """
    pix_on, pix_off = 0.0, 0.0
    bins, binsizes = np.histogram(flat_np)
    bins_asort = np.argsort(bins)[::-1]
    a_idx, b_idx = bins_asort[0], bins_asort[1]
    a_val = (binsizes[a_idx] + binsizes[a_idx+1]) / 2.0
    b_val = (binsizes[b_idx] + binsizes[b_idx+1]) / 2.0
    if a_val < b_val:
        pix_on = a_val
        pix_off = b_val
    else:
        pix_on = b_val
        pix_off = a_val
    return pix_on, pix_off
    
def infer_narrow_wide(lens):
    """ Infers the narrow/wide parameters, given LENS, a list of integers
    representing lengths of regions.
    """
    def get_median_bucket(hist):
        K = int(sum(hist) / 2)
        for i, bucket in enumerate(tuple(hist)):
            if (K-bucket) <= 0:
                return i
            K -= bucket
        print "UH OH, this is weird."
        return 1
    def get_mostpop_bucket(hist):
        idx = np.argmax(hist)
        return idx

    bins, binedges = np.histogram(lens)
    idxs0 = np.where(bins == 0)[0]
    if len(idxs0) == 0:
        idx0 = int(len(bins) / 2)
    else:
        idx0 = idxs0[int(len(idxs0) / 2)]

    binsNarrow = bins[:idx0]
    binsWide = bins[idx0:]
    #narrow_idx = get_median_bucket(binsNarrow)
    #wide_idx = get_median_bucket(binsWide)
    narrow_idx = get_mostpop_bucket(binsNarrow)
    wide_idx = min(get_mostpop_bucket(binsWide)+1, len(binedges))
    narrow = binedges[:idx0][narrow_idx]
    wide = binedges[idx0:][wide_idx]
    return narrow, wide

def is_pix_on(val, pix_on, pix_off):
    return abs(pix_on - val) < abs(pix_off - val)
def w_or_n(cnt, w_narrow, w_wide, step=1):
    return NARROW if (abs((cnt+((step-1)*cnt)) - w_narrow) < abs((cnt+((step-1)*cnt)) - w_wide)) else WIDE

def stripes_to_bars(lens, narrow, wide, imgP=None, T=0.04):
    """ Converts the stripes in LENS to NARROW/WIDE to yield a set of
    possible NARROW/WIDE interpretations. If a stripe's NARROW/WIDE-ness
    is ambiguous, then we generate separate interpretations for each.
    """
    def get_score(x, low, r):
        return 2*((x-low) / r) - 1
    r = wide - narrow
    possibles = [] # [[NARROW_i0/WIDE_i0, ...], [NARROW_i1/WIDE_i1, ...], ...]
    for i, stripe_len in enumerate(lens):
        s = get_score(stripe_len, narrow, r) # -1.0 is perfect narrow, 1.0 is perfect wide
        if abs(s) >= T:
            possibles.append([WIDE if s > 0 else NARROW])
        else:
            print 'ambiguity, s={0}, stripe_len={1}'.format(s, stripe_len)
            possibles.append([WIDE, NARROW])
    # Now, generate all possible interpretations
    interpretations = make_possibles(possibles)
    return interpretations

def make_possibles(lst):
    prevs = []
    for i, vals in enumerate(lst):
        if i == 0:
            prevs = [[v] for v in vals]
        else:
            cur = []
            for v in vals:
                cur.extend([prev+[v] for prev in prevs])
            prevs = cur
    return prevs

def get_i2of5_val(bars):
    """ Given a sequence of narrow/wide, returns the value of the
    sequence, as dictated by Interleaved-2-of-5.
    Input:
        list bars: List of ints, i.e.:
            [NARROW, NARROW, WIDE, WIDE, NARROW]
    Output:
        str decimal value.
    """
    N = NARROW; W = WIDE
    mapping = {(N, N, W, W, N): '0',
               (W, N, N, N, W): '1',
               (N, W, N, N, W): '2',
               (W, W, N, N, N): '3',
               (N, N, W, N, W): '4',
               (W, N, W, N, N): '5',
               (N, W, W, N, N): '6',
               (N, N, N, W, W): '7',
               (W, N, N, W, N): '8',
               (N, W, N, W, N): '9'}
    return mapping.get(tuple(bars), None)
        
def gen_by_n(seq, n):
    """ Outputs elements from seq in N-sized chunks. """
    out, cnt = [], 0
    for i, el in enumerate(seq):
        if cnt == 0:
            out.append(el)
            cnt += 1
        elif cnt % n == 0:
            yield out
            out = [el]
            cnt = 1
        else:
            out.append(el)
            cnt += 1
    if out:
        yield out
        
def bestmatch(A, B):
    """ Tries to find the image A within the (larger) image B.
    For instance, A could be a voting target, and B could be a
    contest.
    Input:
        cvMat A: Patch to search for
        cvMat B: Image to search over
    Output:
        ((x,y), s_mat),  location on B of the best match for A.
    """
    w_A, h_A = A.cols, A.rows
    w_B, h_B = B.cols, B.rows
    s_mat = cv.CreateMat(h_B - h_A + 1, w_B - w_A + 1, cv.CV_32F)
    cv.MatchTemplate(B, A, s_mat, cv.CV_TM_CCOEFF_NORMED)
    minResp, maxResp, minLoc, maxLoc = cv.MinMaxLoc(s_mat)
    return maxLoc, s_mat
def iplimage2cvmat(I):
    w, h = cv.GetSize(I)
    if I.depth == cv.IPL_DEPTH_8U and I.channels == 1:
        cvmat = cv.CreateMat(h, w, cv.CV_8UC1)
    elif I.depth == cv.IPL_DEPTH_32F and I.channels == 1:
        cvmat = cv.CreateMat(h, w, cv.CV_32FC1)
    else:
        cvmat = cv.CreateMat(h, w, cv.CV_8UC1)
    cv.Copy(I, cvmat)
    return cvmat

def dothreshold(I):
    # bins := [ 9358    83    67   119   991  2183   153    64   141 12377]
    # binsizes: [   0.    25.5   51.    76.5  102.   127.5  153.   178.5  204.   229.5  255. ]
    newI = cv.CreateImage(cv.GetSize(I), I.depth, I.channels)
    #I_mat = iplimage2cvmat(I)
    #I_np = np.asarray(I_mat)
    #bins, binsizes = np.histogram(I_np)
    cv.Threshold(I, newI, 35, 255.0, cv.CV_THRESH_BINARY)
    return newI

def get_tempmatches(A, B, T=0.8, do_smooth=True, xwin=13, ywin=13, MAX_MATS=50, atleastone=False):
    """ Runs template matching, trying to find image A within image
    B. Returns location (and responses) of all matches greater than
    some threshold T.
    Input:
        IplImage A:
        IplImage B:
        float T:
    Output:
        list matches, i.e. [(x1, y1, float resp), ...]
    """
    if do_smooth:
        B_smooth = cv.CreateImage(cv.GetSize(B), B.depth, B.channels)
        cv.Smooth(B, B_smooth, cv.CV_GAUSSIAN, param1=xwin,param2=ywin)
        B = B_smooth
    wA, hA = cv.GetSize(A)
    wB, hB = cv.GetSize(B)
    M = cv.CreateMat(hB-hA+1, wB-wA+1, cv.CV_32F)
    cv.MatchTemplate(B, A, M, cv.CV_TM_CCOEFF_NORMED)
    M_np = np.array(M)
    score = np.inf
    #print 'best score:', np.max(M_np)
    num_mats = 0
    matches = []
    while score > T and num_mats < MAX_MATS:
        M_idx = np.argmax(M_np)
        i = int(M_idx / M.cols)
        j = M_idx % M.cols
        score = M_np[i,j]
        if score < T:
            break
        matches.append((j, i, score))
        # Suppression
        M_np[i-(hA/3):i+(hA/3),
             j-(wA/3):j+(wA/3)] = -1.0
        num_mats += 1
    if not matches and atleastone:
        M_idx = np.argmax(M_np)
        i = int(M_idx / M.cols)
        j = M_idx % M.cols
        score = M_np[i,j]
        matches.append((j, i, score))
    return matches

def smooth_constborder(A, xwin=5, ywin=5, val=0):
    """ Smooths A with a Gaussian kernel (with window size [XWIN,YWIN]),
    handling the borders of A by using VAL as the intensity value used
    for pixels outside of A.
    Input:
        IplImage A:
    Output:
        IplImage A_smoothed. 
    """
    wA, hA = cv.GetSize(A)
    A_big = cv.CreateImage((wA+2*xwin, hA+2*ywin), A.depth, A.channels)
    # Pass '0' as bordertype due to undocumented OpenCV flag IPL_BORDER_CONSTANT
    # being 0. Wow!
    cv.CopyMakeBorder(A, A_big, (xwin, ywin), 0, val)
    cv.Smooth(A_big, A_big, cv.CV_GAUSSIAN, param1=xwin, param2=ywin)
    cv.SetImageROI(A_big, (xwin, ywin, wA, hA))
    return A_big
def shiftROI(roi, bb):
    """ Returns a new ROI that is the result of shifting ROI by BB. """
    return (roi[0]+bb[0], roi[1]+bb[1], bb[2], bb[3])

def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("imgpath", help="Imagepath to decode.")
    parser.add_argument("ndigits", type=int, help="Number of digits encoded \
in each barcode.")
    parser.add_argument("--debug", action="store_true")
    return parser.parse_args()

def main():
    args = parse_args()
    imgpath = args.imgpath
    ndigits = args.ndigits
    img = cv.LoadImage(imgpath, cv.CV_LOAD_IMAGE_GRAYSCALE)

    topbot_paths = [[TOP_GUARD_IMGP, BOT_GUARD_IMGP], [TOP_GUARD_SKINNY_IMGP, BOT_GUARD_SKINNY_IMGP]]
    topbot_imgs = [[cv.LoadImage(imP0, cv.CV_LOAD_IMAGE_GRAYSCALE), cv.LoadImage(imP1, cv.CV_LOAD_IMAGE_GRAYSCALE)] for imP0,imP1 in topbot_paths]

    t = time.time()
    print "Starting decode_i2of5 on: {0}...".format(imgpath)
    decoded, bbfull, bbmarks = decode_i2of5(img, ndigits, topbot_imgs, debug=args.debug, imgP=imgpath)
    dur = time.time() - t
    print "...Finished decode_i2of5 ({0} s)".format(dur)
    print "    Decoded: {0} Barcode BB: {1}  [x,y,w,h])".format(decoded, bbfull)
    
if __name__ == '__main__':
    main()
