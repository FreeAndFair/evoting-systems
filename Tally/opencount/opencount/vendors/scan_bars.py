import pdb, os, time
import cv, numpy as np

"""
Parses an image strip containing a series of marks encoding a binary
string, arranged either vertically or horizontally.
"""

"""
Note: The MARKTOL parameter of the parse_mark_maybe function is currently
set at 0.5 to handle cut-off marks. I'm worried that 0.5 is too large
of a tolerance?
"""

VERTICAL = 0
HORIZONTAL = 1

def parse_patch(patch, marksize, gap=7, LEN=None,
                BEGIN_TOL=0.3, END_TOL=0.3, MARKTOL=0.5, 
                orient=HORIZONTAL,
                GAMMA=0.5,
                idx2tol=None):
    """ Interprets a patch with a tight bound.
    Input:
    IplImage PATCH:
    tuple MARKSIZE: (int W, int H)
        The dimensions of each barcode mark.
    int GAP: 
        How much space is between each barcode mark.
    int LEN:
        How many marks the barcode is expected to be. Optional - the default
        value will read as far as it can go.
    float MARKTOL:
        How much tolerance there should be for the width/height of the
        mark during the search. Lower values help detect cut-off marks.
    float BEGIN_TOL, END_TOL:
        How much tolerance there should be for the first/last marks. 
        Only relevant when LEN is some positive integer.
    int ORIENT:
        Which orientation (VERTICAL, HORIZONTAL) the barcode resides in.
    float GAMMA: If you can't find a mark within (GAMMA*w_mark) pixels
                 of the previous mark, then give up. If GAMMA=None, then
                 this behavior is ignored, though, you could get some
                 funky interpretations.
    dict IDX2TOL: {int idx: float TOL}
        Allows you to explicitly specify adjusted mark tolerances to use
        for certain indices of the barcode. Does not override the
        BEGIN_TOL/END_TOL. Like MARKTOL, lower values help detect cut-off
        marks.
    Output:
        (list SYMS, dict PARAMS)
    list SYMS: [(str VAL, int X), ...]
    dict PARAMS: Keys 'pix_on', 'pix_off'.
    """
    w, h = cv.GetSize(patch)
    w_mark, h_mark = marksize

    flat = cv.CreateMat(1, w, cv.CV_32S) if orient == HORIZONTAL else cv.CreateMat(h, 1, cv.CV_32S)
    dim = 0 if orient == HORIZONTAL else 1

    cv.Reduce(patch, flat, dim=dim, op=cv.CV_REDUCE_SUM)
    flat_np = np.asarray(flat)[0] if orient == HORIZONTAL else np.asarray(flat)[:,0]
    flat_tpl = tuple(flat_np)

    pix_on, pix_off = infer_on_off(flat_np)

    syms = scan_line(flat_tpl, w_mark if orient == HORIZONTAL else h_mark, pix_on, pix_off, gap,
                     LEN=LEN, MARKTOL=MARKTOL, BEGIN_TOL=BEGIN_TOL, END_TOL=END_TOL,
                     GAMMA=GAMMA,
                     idx2tol=idx2tol)

    return syms, {'pix_on': pix_on, 'pix_off': pix_off}

def scan_line(data, w_mark, pix_on, pix_off, gap, LEN=None,
              MARKTOL=0.5, BEGIN_TOL=0.3, END_TOL=0.3,
              GAMMA=0.5, idx2tol=None):
    """ Walks DATA, estimating symbols '0'/'1' based on W_MARK and 
    PIX_ON/PIX_OFF.
    Input:
        ...
        float GAMMA: If you can't find a mark within (GAMMA*w_mark) pixels
                     of the previous mark, then give up. If GAMMA=None, then
                     this behavior is ignored, though, you could get some
                     funky interpretations.
    """
    def parse_mark_maybe(data, idx, check_on):
        """ Starting at DATA[IDX], checks to see if an ON/OFF mark
        is present.
        """
        still_good = lambda v: is_on(v) if check_on else not is_on(v)
        i = idx
        run_len = 0
        while i < len(data) and run_len <= w_mark:
            val = data[i]
            if not still_good(val):
                break
            else:
                run_len += 1
                i += 1
        tol = MARKTOL
        cur_sym_idx = len(syms)
        if (LEN != None) and len(syms) == 0:
            tol = BEGIN_TOL
        elif (LEN != None) and len(syms) == (LEN-1):
            tol = END_TOL
        elif idx2tol != None and cur_sym_idx in idx2tol:
            tol = idx2tol[cur_sym_idx]
        low, high = (w_mark*tol), (w_mark*(1.0+(1.0-tol)))
        is_mark = low <= run_len <= high
        #print "== idx={0} data[idx]={4} run_len={1} check_on={2} is_mark={3}".format(idx, run_len, check_on, is_mark, data[idx])
        return is_mark, run_len
    def is_on(x):
        if x <= pix_on or x >= pix_off:
            # Easy case: 'very' on/off
            return x <= pix_on
        else:
            # Choose the closest one
            dist_on, dist_off = abs(x - pix_on), abs(x - pix_off)
            return True if dist_on < dist_off else False
    syms = [] # [(str SYM, int x), ...]
    i = 0
    idx_prevmark = None
    while i < len(data) and ((LEN == None) or (len(syms) < LEN)):
        if GAMMA != None and idx_prevmark != None and abs(i - (idx_prevmark+w_mark+gap)) > (GAMMA * (w_mark+gap)):
            # Terminate 
            return syms
        val = data[i]
        if is_on(val):
            # (Potentially) entering new mark
            is_mark, k = parse_mark_maybe(data, i, True)
            if is_mark:
                syms.append(('1', i))
                idx_prevmark = i
                i += k + gap
            else:
                i += 1
        else:
            # (Potentially) entering '0' mark
            is_mark, k = parse_mark_maybe(data, i, False)
            if is_mark:
                syms.append(('0', i))
                idx_prevmark = i
                i += k + gap
            else:
                i += 1
    return syms

def infer_on_off(data):
    """ Infers the PIX_ON/PIX_OFF values. """
    pix_on, pix_off = 0.0, 0.0
    bins, binsizes = np.histogram(data)
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

def is_img_ext(f):
    return os.path.splitext(f)[1].lower() in ('.png', '.jpg', '.jpeg', '.bmp')

def test_diebold():
    testdir = 'diebold_test'
    # 0.) Gather test data
    test_data = {} # maps {str imgpath: (int orient, str decoding)}
    for dirpath, dirnames, filenames in os.walk(testdir):
        for imgname in [f for f in filenames if is_img_ext(f)]:
            orient = VERTICAL if 'vert' in imgname else HORIZONTAL
            imgpath = os.path.join(dirpath, imgname)
            
            foo = os.path.splitext(imgname)[0].split('_')[0] if orient == VERTICAL else os.path.splitext(imgname)[0]
            resname = foo + '.res'
            respath = os.path.join(dirpath, resname)
            decoding = open(respath, 'r').readlines()[0].strip()
            test_data[imgpath] = (orient, decoding)

    markpath = 'diebold_mark_v2.png'
    mark = cv.LoadImage(markpath, cv.CV_LOAD_IMAGE_GRAYSCALE)
    w, h = cv.GetSize(mark)
    mark_rot = cv.CreateImage((h,w), mark.depth, mark.channels)
    cv.Transpose(mark, mark_rot)

    for i, (imgpath, (orient, decoding)) in enumerate(test_data.iteritems()):
        I = cv.LoadImage(imgpath, cv.CV_LOAD_IMAGE_GRAYSCALE)
        t = time.time()
        syms = parse_patch(I, cv.GetSize(mark) if orient==HORIZONTAL else cv.GetSize(mark_rot), orient=orient)
        dur = time.time() - t

        decoding_guess = ''.join(t[0] for t in syms)
        is_correct = decoding == decoding_guess
        if is_correct:
            print "== CORRECT ({0:.4f}s)".format(dur)

        else:
            print "== WRONG ({0:.4f}s) ({1}!={2})".format(dur, decoding_guess, decoding)
        print "    {0}".format(imgpath)

        # Draw marks
        w_mark, h_mark = cv.GetSize(mark) if orient == HORIZONTAL else cv.GetSize(mark_rot)
        Icolor = cv.LoadImage(imgpath, cv.CV_LOAD_IMAGE_COLOR)
        for idx, (sym, x1) in enumerate(syms):
            if orient == HORIZONTAL:
                cv.Line(Icolor, (x1, 0), (x1, h_mark-1), cv.CV_RGB(230, 0, 0))
                cv.Line(Icolor, (x1+w_mark, 0), (x1+w_mark, h_mark-1), cv.CV_RGB(0, 0, 230))
            else:
                y1 = x1
                cv.Line(Icolor, (0, y1), (w_mark-1, y1), cv.CV_RGB(230, 0, 0))
                cv.Line(Icolor, (0, y1+h_mark-1), (w_mark-1, y1+h_mark-1), cv.CV_RGB(0, 0, 230))

        cv.SaveImage("_Icolor_res_{0}.png".format(i), Icolor)

    return True

def main():
    test_diebold()

if __name__ == '__main__':
    main()
