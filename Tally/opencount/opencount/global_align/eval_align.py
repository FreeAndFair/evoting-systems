import sys, os, pdb, time, cPickle as pickle, math, traceback, argparse, random
import numpy as np, scipy.misc, cv2, matplotlib.pyplot as plt, matplotlib.cm as cm, cv, scipy.stats
import global_align
"""
A script that evaluates alignment methods against a synthetic test set
(generated from eval_create_testset.py).
"""

DESCRIPTION = """A script that quantitatively evaluates different global
alignment methods against a synthetic test set generated from create_testset.py.
"""

STRAT_CV = 'align_cv'
STRAT_LK = 'align_lk'

ALIGN_STRATS_ALL = (STRAT_CV, STRAT_LK)

TRY_ALL_STRATS = 'all'

def standardImread_v2(imgpath, flatten=False, dtype='float32', normalize=True):
    """ Reads in IMGPATH, and outputs a numpy array with pix. If normalize
    is True, then intensity values will be floats from [0.0, 1.0]. O.w.
    will be ints from [0, 255].
    """
    cvmode = cv.CV_LOAD_IMAGE_GRAYSCALE if flatten else cv.CV_LOAD_IMAGE_COLOR
    Icv = cv.LoadImageM(imgpath, cvmode)
    Inp = np.asarray(Icv, dtype=dtype)
    if normalize:
        Inp = Inp / 255.0
    return Inp

def fastFlip(I):
    Icv=cv.fromarray(np.copy(I))
    I1cv=cv.CreateMat(I.shape[0],I.shape[1],Icv.type)
    cv.Flip(Icv,I1cv,-1)
    Iout=np.asarray(I1cv)
    return Iout

def apply_varyContrast_patches(I, N, PATCH_W, PATCH_H, ALPHA, WITHIN=0.05, maxPixVal=1.0, BBOXES=None):
    """ Randomly places N patches of size (PATCH_W, PATCH_H) on image I,
    and varys the contrast of the patch by multiplying the patch intensity
    values by an amount ALPHA.
    WITHIN dictates that the patch locations must be >= 0.1*w and 0.1*h, etc.
    MAXPIXVAL is used to determine how to saturate intensity values.
    Reasonable values for ALPHA are 0.85 (slightly darken), 1.1 (slightly brighten).
    Output:
        nparray IOUT, int NUM_PIXS_AFFECTED
    """
    h, w = I.shape
    if not BBOXES:
        N = int(N)
        y_low, y_high = (int(round(h * WITHIN)), int(round(h * (1.0 - WITHIN)) - PATCH_H))
        x_low, x_high = (int(round(w * WITHIN)), int(round(w * (1.0 - WITHIN)) - PATCH_W))
        xs, ys = random.sample(xrange(x_low, x_high), N), random.sample(xrange(y_low, y_high), N)
        maskAlpha = np.ones(I.shape, dtype=I.dtype)
        for i, x1 in enumerate(xs):
            y1 = ys[i]
            maskAlpha[y1:min(h, y1+PATCH_H), x1:min(w, x1+PATCH_W)] = ALPHA
    else:
        maskAlpha = np.ones(I.shape, dtype=I.dtype)
        for (x1,y1,x2,y2) in BBOXES:
            maskAlpha[max(0, y1):min(h, y2), max(0, x1):min(w, x2)] = ALPHA
    Iout = I * maskAlpha
    Iout[np.where(Iout > maxPixVal)] = maxPixVal # Saturate
    num_pixs = len(np.where(maskAlpha == ALPHA)[0])
    return Iout, num_pixs

def eval_testset(testsetdir, align_strat=STRAT_CV,
                 debug=False, CACHE_IMG=None, NUM_BALLOTS=None,
                 cropx=0.02, cropy=0.02, rszfac=0.15,
                 CONTRAST_NUM=None, CONTRAST_W=None, CONTRAST_H=None, CONTRAST_ALPHA=None,
                 CONTRAST_BBOXES=None,
                 alt_refimgpath=None,
                 minArea=None,
                 show_overlays_interactive=False,
                 show_progress=True):
    """ Evaluates the global alignment method on a testset.
    Output:
        dict ERRS_MAP, list ERRS, list ERRS_X, list ERRS_Y, list ERRS_THETA, float DUR_TOTAL, dict USERDATA
    dict ERRS_MAP: {(srcimgP, dstimgP): (P_expected, P_estimate)}
        where P_* := (int X, int Y, float THETA, int BRIGHT_AMT)
    """
    # dict SRC2DSTS: {str srcimgP: tuple (dstimgP, x, y, theta, bright_amt)}
    #     If DSTIMGP is None, then this means I should warp SRCIMGP by the
    #     prescribed amts.
    src2dsts = pickle.load(open(os.path.join(testsetdir, 'src2dsts.p'), 'rb'))
    # dict DST2SRC: {str dstimgP: str srcimgP}
    dst2src = pickle.load(open(os.path.join(testsetdir, 'dst2src.p'), 'rb'))
    # dict SRC2FLIP: {str srcimgP: bool isFlip} Note: dsts have already been correctly flipped
    src2flip = pickle.load(open(os.path.join(testsetdir, 'src2flip.p')))

    FLAG_EXP_VARY_CONTRAST = CONTRAST_NUM == None and CONTRAST_ALPHA != None
    
    errs = []
    errs_x, errs_y, errs_theta = [], [], []
    errs_map = {} # maps {(str srcimgP, str dstimgP): (tuple P_EXPECTED, tuple P_ESTIMATED)}
    userdata = {}
    t_start = time.time()
    def load_img(imP, dtype='float32', normalize=True):
        if alt_refimgpath != None:
            imP = alt_refimgpath
        I = CACHE_IMG.get(imP, None) if CACHE_IMG else None
        if I == None:
            I = standardImread_v2(imP, flatten=True, dtype=dtype, normalize=normalize)
            if CACHE_IMG != None:
                CACHE_IMG[imP] = I
        return I
    if NUM_BALLOTS == None:
        N = len(src2dsts) * len(src2dsts[src2dsts.keys()[0]])
    else:
        N = NUM_BALLOTS * len(src2dsts[src2dsts.keys()[0]])
    i = 0
    t_prev = time.time()
    step = N / 10 # Print out at each 10% interval
    step = 1 if step == 0 else step
    def update_status():
        if i == 0:
            return False
        t_cur = time.time()
        dur_step = t_cur - t_prev
        n_remain = N - i
        est = ((dur_step / float(step)) * n_remain) / 60.0 # est. time left in minutes
        if i % step == 0:
            print "...{0:.2f}% complete... ({1} left, {2:.4f} min. left)".format(100.0 * (i / float(N)), n_remain, est)
            return True
        return False
    def plotimages(I, Iref, Ireg, x_, y_, theta_, x, y, theta, err):
        A = Iref + Ireg
        fig = plt.figure(figsize=(18, 10))
        fig.suptitle("(Found):  x={0:.2f} y={1:.2f} theta={2:.3f}\n\
(Expect): x={3:.2f} y={4:.2f} theta={5:.3f}\n\
Err={6:.4f}".format(x_, y_, theta_, x, y, theta, err))
                     
        plt_Iref = fig.add_subplot(221)
        plt_Iref.set_title("Iref")
        plt_Iref.imshow(Iref, cmap=cm.Greys_r)
        plt_I = fig.add_subplot(222)
        plt_I.set_title("I")
        plt_I.imshow(I, cmap=cm.Greys_r)
        plt_Ireg = fig.add_subplot(223)
        plt_Ireg.set_title("Ireg")
        plt_Ireg.imshow(Ireg, cmap=cm.Greys_r)
        plt_overlay = fig.add_subplot(224)
        plt_overlay.set_title("Overlay")
        plt_overlay.imshow(A, cmap=cm.Greys_r)
        fig.show()
        return fig

    for refimgpath, dst_tpls in sorted(src2dsts.iteritems()):
        if N != None and i >= N:
            break
        if align_strat == STRAT_LK:
            Iref_orig = load_img(refimgpath, dtype='float32', normalize=True)
        else:
            Iref_orig = load_img(refimgpath, dtype='uint8', normalize=False)
        if src2flip and src2flip.get(refimgpath, False):
            Iref_orig = fastFlip(Iref_orig)
        if CONTRAST_BBOXES != None:
            maxPixVal = 255.0 if Iref_orig.dtype == 'uint8' else 1.0
            Iref, num_pixels = apply_varyContrast_patches(Iref_orig, None, None, None, CONTRAST_ALPHA, maxPixVal=maxPixVal, BBOXES=CONTRAST_BBOXES)
        elif CONTRAST_NUM != None:
            maxPixVal = 255.0 if Iref_orig.dtype == 'uint8' else 1.0
            Iref, num_pixels = apply_varyContrast_patches(Iref_orig, CONTRAST_NUM, CONTRAST_W, CONTRAST_H, CONTRAST_ALPHA, maxPixVal=maxPixVal)
        elif CONTRAST_ALPHA != None:
            maxPixVal = 255.0 if Iref_orig.dtype == 'uint8' else 1.0
            Iref = varyContrast(Iref_orig, CONTRAST_ALPHA, maxPixVal=maxPixVal)
        else:
            Iref = Iref_orig

        for (dstimgpath, x, y, theta, bright_amt) in sorted(dst_tpls, key=lambda t: t[0]):
            # X,Y,THETA are the amts. by which IREF was perturbed to create I.
            # If X,Y=-50,-50, then IREF was shifted left 50 pixels, up 50 pixels to create I.
            # Here, Negative THETA is clock-wise, Positive THETA is counter-clockwise.
            if show_progress:
                did_update = update_status()
                if did_update:
                    t_prev = time.time()
            if align_strat == STRAT_CV:
                if dstimgpath != None:
                    I = standardImread_v2(dstimgpath, dtype='uint8', normalize=False, flatten=True)
                else:
                    I = warp_img(Iref, x, y, theta, bright_amt)
                if FLAG_EXP_VARY_CONTRAST:
                    I_inkmean, I_inkstd = estimate_inkstats(I, THRESHOLD=0.9)
                    Iref_inkmean, Iref_inkstd = estimate_inkstats(Iref, THRESHOLD=0.9)
                    userdata.setdefault('inkstats', []).append((I_inkmean, I_inkstd, Iref_inkmean, Iref_inkstd))

                H, Ireg, err = global_align.align_cv(I, Iref, computeErr=True, crop=(cropx, cropy))
                x_ = -H[0,2]
                y_ = -H[1,2]
                theta_ = -math.degrees(H[0,1])
                x_err = x_ - x
                y_err = y_ - y
                theta_err = theta_ - theta
            elif align_strat == STRAT_LK:
                if dstimgpath != None:
                    I = standardImread_v2(dstimgpath, dtype='float32', normalize=True, flatten=True)
                else:
                    I = warp_img(Iref, x, y, theta, bright_amt)
                if FLAG_EXP_VARY_CONTRAST:
                    I_inkmean, I_inkstd = estimate_inkstats(I, THRESHOLD=0.9)
                    Iref_inkmean, Iref_inkstd = estimate_inkstats(Iref, THRESHOLD=0.9)
                    userdata.setdefault('inkstats', []).append((I_inkmean, I_inkstd, Iref_inkmean, Iref_inkstd))

                H, Ireg, err_ = global_align.align_image(I, Iref, verbose=False,
                                                         CROPX=cropx, CROPY=cropy, RSZFAC=rszfac,
                                                         MINAREA=minArea)
                err = np.mean(np.abs(Ireg - Iref_orig))
                # H is an Affine matrix:
                #     [cos(R) , sin(R), t_x]
                #     [-sin(R), cos(R), t_y]
                #     [   0   ,   0   ,  1 ]
                # Note that H is living in ORIGIN coordinates (e.g. the
                # center of the image). In particular, t_x/t_y are NOT simply the 
                # translation amounts.
                # To transform a point P (in IMAGE coords):
                #     P_trans := T0 . H . T1 . P    ('.' is matrix multiplication)
                # where T0 := Shifts from ORIGIN to (0,0)
                #       T1 := Shifts from (0,0) to ORIGIN
                x_, y_ = recover_xy_trans(H, I.shape[1], I.shape[0])
                x_ = -x_ # Multiply by -1.0 to "undo" the translation
                y_ = -y_
                # negative theta -> counter-clockwise
                theta_ = -1.0 * recover_theta_rot(H)
                x_err = x_ - x
                y_err = y_ - y
                theta_err = theta_ - theta
            else:
                raise Exception("Unrecognized alignment strategy: {0}".format(align_strat))
            errs_x.append(x_err)
            errs_y.append(y_err)
            errs_theta.append(theta_err)
            P_expected = (x, y, theta, bright_amt)
            P_estimate = (x_, y_, theta_, None)
            errs_map[(refimgpath, dstimgpath)] = (P_expected, P_estimate)
            errs.append(err)
            if show_overlays_interactive:
                print H
                print "(Found): x={0} y={1} theta={2}".format(x_, y_, theta_)
                print "(Expect): x={0}, y={1}, theta={2}".format(x,y,theta)
                print "Err:", err
                print "x_err={0} y_err={1} theta_err={2}".format(x_err, y_err, theta_err)
                fig = plotimages(I, Iref_orig, Ireg, x_, y_, theta_, x, y, theta, err)
                pdb.set_trace()
            i += 1

    dur_total = time.time() - t_start
    return errs_map, errs, errs_x, errs_y, errs_theta, dur_total, userdata

def recover_xy_trans(H, w, h):
    """ Returns the x,y translation encoded in the H affine matrix. Assume
    H is in origin-coordinates.
    """
    # T0: Transforms (0,0) to image center
    T0=np.eye(3); T0[0,2]=w/2.0; T0[1,2]=h/2.0
    # T1: Transforms image center to (0,0)
    T1=np.eye(3); T1[0,2]=-w/2.0; T1[1,2]=-h/2.0
    H1 = np.dot(T0, np.dot(H, T1)) # H1 inputs image-coords, outputs image-coords
    theta = math.radians(recover_theta_rot(H))
    Hrot = np.array([[math.cos(theta), math.sin(theta), 0.0],
                     [-math.sin(theta), math.cos(theta), 0.0],
                     [0.0, 0.0, 1.0]])
    # Assumes that H1 is of the form:
    #         H1 = T . T0 . R . T1    ('.' denotes matrix mult)     (1)
    # Where:
    #     T1  := Shifts image-coords -> origin-coords
    #     R   := Rotation matrix (in origin-coords)
    #     T0  := Shifts origin-coords -> image-coords
    #     T   := Translation matrix (in image-coords)
    # Recover the translation matrix T via manipulations to eq. (1)
    T = np.dot(H1, np.dot(np.linalg.inv(T1), np.dot(np.linalg.inv(Hrot), np.linalg.inv(T0))))
    return T[0,2], T[1,2]

def recover_theta_rot(H):
    """ Recovers the theta rotation of H (in degrees). Assumes H is in
    image coordinates.
    Outputs theta s.t. positive theta is counter-clockwise,
                       negative theta is clockwise
    """
    '''
    Minor annoyance: Recall that there are two separate rotation matrices:
        | cos(R) , sin(R) |        | cos(R) , -sin(R) |
        |-sin(R) , cos(R) |        | sin(R) ,  cos(R) | 
      In the left one, positive R implies counter-clockwise rotation.
      In the right one, positive R implies clockwise rotation.
    We need to disambiguate this to always return theta s.t.
        Positive theta -> counter-clockwise rotation.
    '''
    H00 = min(max(H[0,0], -1.0), 1.0) # clamp to [-1.0, 1.0] to avoid numerical instability
    H01 = min(max(H[0,1], -1.0), 1.0)
    H10 = min(max(H[0,1], -1.0), 1.0)
    theta_0 = math.degrees(math.acos(H00))
    theta_1 = math.degrees(math.asin(H01))
    if theta_0 >= 0.0 and theta_1 >= 0.0:
        # theta is in counter-clockwise mode
        return theta_0
    else:
        # theta is in clockwise mode
        return -theta_0

def make_affine_mat(x, y, theta, w, h):
    """ Creates affine mat, rotating w.r.t. image center. Assumes that
    THETA is in radians. Outputs the affine mat H that is in image-coordinates.
    """
    T1, T0 = np.eye(3), np.eye(3)
    T1[0,2] = -w / 2.0
    T1[1,2] = -h / 2.0
    Hrot = np.array([[math.cos(theta), math.sin(theta), 0.0],
                     [-math.sin(theta), math.cos(theta), 0.0],
                     [0.0, 0.0, 1.0]])
    T0[0,2] = w / 2.0
    T0[1,2] = h / 2.0
    S = np.eye(3)
    S[0,2] = x
    S[1,2] = y
    H_out = np.dot(S, np.dot(T0, np.dot(Hrot, T1)))
    return H_out

def warp_img(I, x, y, theta, bright_amt):
    """ Warps image I by translating by (X,Y), rotating by THETA, and 
    adding BRIGHT_AMT to the intensities. Theta is in degrees, counter-clockwise
    rotation for positive theta.
    """
    h, w = I.shape
    Itrans = np.zeros(I.shape, dtype=I.dtype)

    Itrans[max(0, y):min(h, h + y), max(0, x):min(w, w + x)] = I[max(0, -y):min(h, h-y), max(0, -x):min(w, w - x)]
    Iout = Itrans
    if theta != 0.0:
        # scipy.ndimage.rotate: Counter-clockwise rotation for positive theta
        Iout = scipy.ndimage.rotate(Iout, theta, reshape=False)
    if bright_amt != None:
        Iout += bright_amt
    return Iout

def plot_hist(data, plot, width=None, **kwargs):
    hist, bins = np.histogram(data, bins = 50)
    if width == None:
        width = 0.7*(bins[1]-bins[0])
    center = (bins[:-1]+bins[1:])/2
    b = plot.bar(center, hist, align = 'center', width = width, **kwargs)
    return b

def plot_errs(errs_map, errs, errs_x, errs_y, errs_theta):
    fig = plt.figure()

    # Plot I_sad errs distribution
    plt_Isad = fig.add_subplot(221)
    plt_Isad.set_title("Sum of Abs. Diffs. Btwn. Isrc/Idst")
    plt_Isad.set_xlabel("Error")
    plt_Isad.set_ylabel("Num. Occurrences")
    plot_hist(errs, plt_Isad)

    # Plot X errs dist.
    plt_err_x = fig.add_subplot(222)
    plt_err_x.set_title("X Param. Error")
    plt_err_x.set_xlabel("Error")
    plt_err_x.set_ylabel("Num. Occurrences")
    plot_hist(errs_x, plt_err_x)

    # Plot Y errs dist.
    plt_err_y = fig.add_subplot(223)
    plt_err_y.set_title("Y Param. Error")
    plt_err_y.set_xlabel("Error")
    plt_err_y.set_ylabel("Num. Occurrences")
    plot_hist(errs_y, plt_err_y)

    # Plot Theta errs dist.
    plt_err_theta = fig.add_subplot(224)
    plt_err_theta.set_title("Theta Param. Error")
    plt_err_theta.set_xlabel("Error")
    plt_err_theta.set_ylabel("Error")
    plot_hist(errs_theta, plt_err_theta)

    fig.show()
    raw_input("Enter to continue.")

def experiment_vary_crop(args):
    """ Run an experiment by varying the CROP parameter. """
    testsetdir = args.testsetdir
    outpath = args.out
    align_strat = args.align_strat
    interactive_overlays = args.interactive
    debug = args.debug
    N = args.n
    def get_nums():
        src2dsts = pickle.load(open(os.path.join(testsetdir, 'src2dsts.p')))
        num_ballots = args.n if args.n != None else len(src2dsts)
        num_alignments = num_ballots * len(src2dsts[src2dsts.keys()[0]])
        return num_ballots, num_alignments
    num_ballots, num_alignments = get_nums()

    if args.crop_box == None:
        cropX, cropXSTEP, cropY, cropYSTEP = args.crop
    else:
        cropX, cropXSTEP = args.crop_box
        cropY, cropYSTEP = cropX, cropXSTEP

    rszfacLOW, rszfacMAX, rszfacSTEP = args.rszFacs
    cropXs = (cropX,) if cropXSTEP == 0 else np.linspace(0.0, cropX, num=math.ceil(cropX / cropXSTEP), endpoint=True)
    cropYs = (cropY,) if cropYSTEP == 0 else np.linspace(0.0, cropY, num=math.ceil(cropY / cropYSTEP), endpoint=True)
    rszfacs = (rszfacLOW,) if (rszfacMAX == 0 or rszfacSTEP == 0) else np.linspace(rszfacLOW, rszfacHIGH, endpoint=True,
                                                                                   num=math.ceil((rszfacHIGH - rszfacLOW) / rszfacSTEP))
    def plot_err_vs_crop(errs_all):
        """ Plots the AggregateError vs. a 'single' crop parameter C. C only considers
        choices of CROPX/CROPY where CROPX == CROPY.
        The 'AggregateError' is computed by summing:
            AggError = (Error_0 + Error_1 + ... + Error_N) / N
        Where:
            Error_i = abs(p_star_i - p_i) / max(p_star_i, p_i)  ranges from [0.0, 1.0]
        """
        def get_aggregate_error_P(P_expected, P_found):
            """ Outputs the rootmeansquare (RMS) deviation between inputs. Note
            that this is a bit unprincipled, since X/Y are diff. units than theta.
            """
            err_out = 0.0
            num_rel_params = 0
            for i, p_star_i in enumerate(P_expected):
                p_i = P_found[i]
                if p_star_i == None or p_i == None:
                    continue
                err_out += (p_star_i - p_i)**2.0
                num_rel_params += 1
                '''
                if p_star_i == 0 and p_i == 0:
                    continue
                agg_err = abs(p_star_i - p_i) / max(abs(p_star_i), abs(p_i))
                err_out += agg_err
            err_out_norm = err_out / float(num_rel_params) # normalize to range from [0.0, 1.0]
            print "err_out_norm: {0:.4f}".format(err_out_norm)
            return err_out_norm
                '''
            if np.isinf(err_out) or np.isnan(err_out):
                print "Uhoh, err_out was: {0}".format(err_out)
                pdb.set_trace()
            if num_rel_params == 0:
                print "WOAH"
                pdb.set_trace()
            return math.sqrt(err_out / num_rel_params)

        fig = plt.figure()
        str_cropXs = "[" + ' '.join(["{0:.3f}".format(c_amt) for c_amt in cropXs]) + "]"
        fig.suptitle("Experiment: varyCrop (testset={0}, align_strat={1}, num_ballots={2} num_alignments={3})\n\
Crops={4}".format(testsetdir, align_strat, num_ballots, num_alignments, str_cropXs))
        
        p0 = fig.add_subplot(321)
        p0.set_title("CropBox Param vs. Aggregate Param. Error")
        p0.set_xlabel("Crop Amt.")
        p0.set_ylabel("Root-Mean-Square (RMS) deviation")

        crop_vs_Xerrs, crop_vs_Yerrs, crop_vs_Terrs = {}, {}, {} # maps {float CROP: [err_0, ...]}
        crop_vs_L1norms = {}
        crop2aggerrs = {} # maps {float CROP: [aggerr_p_0, ...]}
        for (cropx, cropy, rszfac), data in errs_all.iteritems():
            # dict errs_map: maps {(srcpath, dstpath): (P_expected, P_found)}
            errs_map, errs, errs_x, errs_y, errs_theta, dur = data
            if not np.allclose(cropx, cropy):
                continue
            crop_vs_Xerrs[cropx] = np.abs(errs_x)
            crop_vs_Yerrs[cropx] = np.abs(errs_y)
            crop_vs_Terrs[cropx] = np.abs(errs_theta)
            crop_vs_L1norms[cropx] = errs
            for (srcpath, dstpath), (P_expected, P_found) in errs_map.iteritems():
                crop2aggerrs.setdefault(cropx, []).append(get_aggregate_error_P(P_expected, P_found))

        xs_0, ys_0 = [], []

        CIs = []
        # http://ww1.cpa-apc.org:8080/publications/archives/PDF/1996/Oct/strein2.pdf
        for crop, aggerrs_p in sorted(crop2aggerrs.iteritems()):
            mean, std = np.mean(aggerrs_p), np.std(aggerrs_p)
            xs_0.append(crop)
            ys_0.append(mean)
            SE = std / math.sqrt(len(aggerrs_p)) # Standard Error (SE)
            CIs.append(1.96 * SE) # 95% Confidence Interval (CI)
    
        p0.errorbar(xs_0, ys_0, yerr=CIs, fmt='ro')

        def plot_aggregate_stats(x_vs_ys, plot):
            """ Plots error-bars aggStats on input data.
            Input:
                dict X_VS_YS: {float X: [float y_0, y_1, ...]}
                Plot PLOT
            """
            xs_, ys_ = [], []
            CIs = []
            for x, ys in sorted(x_vs_ys.iteritems()):
                mean, std = np.mean(ys), np.std(ys)
                SE = std / math.sqrt(len(ys))
                CIs.append(1.96 * SE)
                xs_.append(x); ys_.append(mean)
            plot.errorbar(xs_, ys_, yerr=CIs, fmt='ro')
            return plot

        p1 = fig.add_subplot(322)
        p1.set_title("CropBox Param vs. Abs X Error")
        p1.set_xlabel("Crop Amt.")
        p1.set_ylabel("Abs. X Error (Pixels)")
        plot_aggregate_stats(crop_vs_Xerrs, p1)
        
        p2 = fig.add_subplot(323)
        p2.set_title("CropBox Param. vs. Abs Y Error")
        p2.set_xlabel("Crop Amt.")
        p2.set_ylabel("Abs. Y Error (Pixels)")
        plot_aggregate_stats(crop_vs_Yerrs, p2)

        p3 = fig.add_subplot(324)
        p3.set_title("CropBox Param. vs. Abs Theta Error")
        p3.set_xlabel("Crop Amt.")
        p3.set_ylabel("Abs. Theta Error (Degrees)")
        plot_aggregate_stats(crop_vs_Terrs, p3)

        p4 = fig.add_subplot(325)
        p4.set_title('CropBox Param. vs. Sum-of-Intensity-Errors')
        p4.set_xlabel("Crop Amt.")
        p4.set_ylabel("L1 norm, from [0.0,1.0], 0.0 is 'perfect'")
        plot_aggregate_stats(crop_vs_L1norms, p4)

        fig.show()
        pdb.set_trace()

    print "...Evaluating the testset at: {0} (with align_strat={1})".format(testsetdir, align_strat)
    if not args.crop_box:
        print "    cropXs: {0}".format(cropXs)
        print "    cropYs: {0}".format(cropYs)
    else:
        print "    crops: {0}".format(cropXs)
    print "    rszFacs: {0}".format(rszfacs)
    errs_all = {} # maps {(cropx, cropy, rszfac): (errs_map, errs, errs_x, errs_y, errs_theta, dur)}
    iter_i = 0
    t_total = time.time()
    for cropx in cropXs:
        for cropy in cropYs:
            if args.crop_box != None and cropy != cropx:
                continue
            for rszfac in rszfacs:
                print "(Iter {0}/{1}) Doing cropx={2:.3f} cropy={3:.3f} rszfac={4:.3f}...".format(iter_i, len(cropXs), cropx, cropy, rszfac)
                t = time.time()
                # dict errs_map: maps {(srcpath, dstpath): (P_expected, P_found)}
                errs_map, errs, errs_x, errs_y, errs_theta, dur, _ = eval_testset(testsetdir, align_strat=align_strat,
                                                                                  debug=debug, NUM_BALLOTS=N,
                                                                                  show_overlays_interactive=interactive_overlays,
                                                                                  cropx=cropx, cropy=cropy, rszfac=rszfac,
                                                                                  show_progress=False)
                errs_all[(cropx, cropy, rszfac)] = (errs_map, errs, errs_x, errs_y, errs_theta, dur)
                dur = time.time() - t
                print "...Finished iter {0}/{1} ({2:.4f}s)".format(iter_i, len(cropXs), dur)
                iter_i += 1
    dur_total = time.time()
    print "Done. ({0:.4f}s total)".format(dur_total - t_total)
    plot_err_vs_crop(errs_all)

def experiment_compare_align_strats(args):
    """ Empirically compare different alignment strategies. """
    testsetdir = args.testsetdir
    outpath = args.out
    align_strat = args.align_strat
    debug = args.debug
    N = args.n

    def get_crop_params():
        """ Ignores the STEP params. """
        if args.crop_box != None:
            return args.crop_box[0], args.crop_box[0]
        else:
            return args.crop[0], args.crop[2]

    cropx, cropy = get_crop_params()
    print "cropx={0:.3f} cropy={1:.3f}".format(cropx, cropy)

    strat2L1norms = {}
    strat2xerrs, strat2yerrs, strat2terrs = {}, {}, {}
    strat2goodbadcnts = {} # maps {str align_strat: {(int X_TOL, int Y_TOL, float T_TOL): (int cnt_goodAligns, int cnt_badAligns)}}
    strat2outliers = {} # maps {str align_strat: [(str srcpath, str dstpath, P_expected, P_found), ...]}
    def is_good_align(P_expected, P_found, X_TOL=6, Y_TOL=6, T_TOL=0.05):
        """ Returns True if P_FOUND is reasonably close to P_EXPECTED. """
        x_star, y_star, theta_star, brightamt_star = P_expected
        x_, y_, theta_, brightamt_ = P_found
        return abs(x_star - x_) <= X_TOL and abs(y_star - y_) <= Y_TOL and abs(theta_star - theta_) <= T_TOL

    _GOODBAD_NUMSTEPS = 20
    TRANS_TOLS = np.linspace(0.0, 40, num=_GOODBAD_NUMSTEPS, endpoint=True)
    THETA_TOLS = np.linspace(0.0, 0.5, num=_GOODBAD_NUMSTEPS, endpoint=True)
    for i_align, align_strat in enumerate(ALIGN_STRATS_ALL):
        print "({0}/{1} align_strat={2})".format(i_align+1, len(ALIGN_STRATS_ALL), align_strat)
        t = time.time()
        errs_map, errs, errs_x, errs_y, errs_theta, dur, _ = eval_testset(testsetdir, align_strat=align_strat,
                                                                          debug=debug, NUM_BALLOTS=N,
                                                                          cropx=cropx, cropy=cropy,
                                                                          show_overlays_interactive=args.interactive)
        dur = time.time() - t
        print "Done ({0:.4f}s) (Iter {1}/{2})".format(dur, i_align+1, len(ALIGN_STRATS_ALL))
        strat2xerrs[align_strat] = errs_x
        strat2yerrs[align_strat] = errs_y
        strat2terrs[align_strat] = errs_theta
        strat2L1norms[align_strat] = errs
        for step in xrange(_GOODBAD_NUMSTEPS):
            TRANS_TOL, THETA_TOL = TRANS_TOLS[step], THETA_TOLS[step]
            cnt_goodAlign, cnt_badAlign = 0, 0
            for (srcpath, dstpath), (P_expected, P_found) in errs_map.iteritems():
                if is_good_align(P_expected, P_found, X_TOL=TRANS_TOL, Y_TOL=TRANS_TOL, T_TOL=THETA_TOL):
                    cnt_goodAlign += 1
                else:
                    cnt_badAlign += 1
                    if step == _GOODBAD_NUMSTEPS - 1:
                        strat2outliers.setdefault(align_strat, []).append((srcpath, dstpath, P_expected, P_found))
            strat2goodbadcnts.setdefault(align_strat, {})[(TRANS_TOL, TRANS_TOL, THETA_TOL)] = cnt_goodAlign, cnt_badAlign
    def get_nums():
        src2dsts = pickle.load(open(os.path.join(testsetdir, 'src2dsts.p')))
        num_ballots = args.n if args.n != None else len(src2dsts)
        num_alignments = num_ballots * len(src2dsts[src2dsts.keys()[0]])
        return num_ballots, num_alignments

    num_ballots, num_alignments = get_nums()

    fig_accs = plt.figure()
    fig_accs.suptitle("Experiment: CompareAligns. Alignment Accuracy (Num Ballots={1} Num Alignments={2})\n\
testset={3}".format(align_strat, num_ballots, num_alignments, testsetdir))

    p_accs = fig_accs.add_subplot(111)
    p_accs.set_title("Accuracy")
    p_accs.set_xlabel("Allowed Slack. 0 is most strict (perfect), end allows {0} pixel translation, {1} degree rotation slack.".format(TRANS_TOLS[-1], THETA_TOLS[-1]))
    p_accs.set_ylabel("Percentage of 'Good' Alignments")
    p_accs.set_xticks(xrange(1, len(strat2goodbadcnts[strat2goodbadcnts.keys()[0]])))
    COLORS = ("b", "r", "g")

    for i_align, (align_strat, tols2cnts) in enumerate(sorted(strat2goodbadcnts.iteritems())):
        accs = []
        for (X_TOL, Y_TOL, THETA_TOL), (cnt_good, cnt_bad) in sorted(tols2cnts.iteritems(), key=lambda pair: pair[0][0]):
            accs.append(cnt_good / float(cnt_good + cnt_bad))
        line = p_accs.plot(accs, color=COLORS[i_align], label=align_strat)
    p_accs.legend()

    fig_accs.show()
    
    for align_strat, outliers in sorted(strat2outliers.iteritems()):
        print "{0} outliers for align_strat={1}".format(len(outliers), align_strat)

    fig = plt.figure()
    titletext = "Compare Alignment Methods (Num. Ballots={0} Num. Alignments={1}) {2}".format(num_ballots, num_alignments, ALIGN_STRATS_ALL)
    for align_strat in ALIGN_STRATS_ALL:
        xerr_mean, xerr_std = np.mean(strat2xerrs[align_strat]), np.std(strat2xerrs[align_strat])
        yerr_mean, yerr_std = np.mean(strat2yerrs[align_strat]), np.std(strat2yerrs[align_strat])
        terr_mean, terr_std = np.mean(strat2terrs[align_strat]), np.std(strat2terrs[align_strat])
        L1_mean, L1_std = np.mean(strat2L1norms[align_strat]), np.std(strat2L1norms[align_strat])
        titletext += "\n"
        titletext += "align_strat={0}\n".format(align_strat)
        titletext += "    XERR mean/std={0:.2f}, {1:.2f}".format(xerr_mean, xerr_std)
        titletext += " YERR mean/std={0:.2f}, {1:.2f}".format(yerr_mean, yerr_std)
        titletext += " TERR mean/std={0:.3f}, {1:.3f}".format(terr_mean, terr_std)
        titletext += " L1 mean/std={0:.5f}, {1:.5f}\n".format(L1_mean, L1_std)
                                  
    fig.suptitle(titletext)
    
    def plot_stacked_hists(strat2data, plot):
        COLORS = ("b", "r", "g")
        bars = [] # [(str align_strat, Plot bargraph)]
        width = 0.0
        for _, data in strat2data.iteritems():
            hist, bins = np.histogram(data, bins=50)
            width = max(width, 0.7 * (bins[1] - bins[0]))
        for i_align, (align_strat, data) in enumerate(sorted(strat2data.iteritems())):
            COLOR = COLORS[i_align]
            bar = plot_hist(data, plot, color=COLOR, alpha=0.5, width=width)
            hist, bins = np.histogram(data, bins=50)
            plot.axvline(x=bins[0], color=COLOR)
            plot.axvline(x=bins[-1], color=COLOR)
            bars.append((align_strat, bar))
        plot.legend([b[1][0] for b in bars], [b[0] for b in bars])
        return plot

    p0 = fig.add_subplot(221)
    p0.set_title("X errors histograms")
    p0.set_xlabel("X error (pixels)")
    plot_stacked_hists(strat2xerrs, p0)
    
    p1 = fig.add_subplot(222)
    p1.set_title("Y errors histograms")
    p1.set_xlabel("Y error (pixels)")
    plot_stacked_hists(strat2yerrs, p1)

    p2 = fig.add_subplot(223)
    p2.set_title("Theta errors histograms")
    p2.set_xlabel("Theta errors (degrees)")
    plot_stacked_hists(strat2terrs, p2)

    p3 = fig.add_subplot(224)
    p3.set_title("L1 norms histograms")
    p3.set_xlabel("L1 norm error (ranges from [0.0,1.0])")
    plot_stacked_hists(strat2L1norms, p3)

    fig.show()

    pdb.set_trace()

def varyContrast(I, ALPHA, THRESHOLD=0.9, maxPixVal=1.0):
    """ Multiplies pixel intensity values of I by ALPHA for all pixels
    whose intensity value is <=THRESHOLD. Intensity values should range
    from [0.0, 1.0].
    Input:
        nparray I:
        float ALPHA:
        float THRESHOLD:
    Output:
        nparray IOUT.
    """
    alphaMask = np.ones(I.shape, dtype='float32')
    alphaMask[np.where(I < THRESHOLD)] = ALPHA
    Iout = I * alphaMask
    Iout[np.where(Iout > maxPixVal)] = maxPixVal # Saturate
    return Iout

def estimate_inkstats(I, THRESHOLD=0.9):
    """ Returns the mean, std of pixel intensity values of the INK on the image. """
    mask = np.zeros(I.shape, dtype=I.dtype)
    mask[:,:] = np.nan
    idxs = np.where(I < THRESHOLD)
    mask[idxs] = 1.0
    area = len(idxs[0])
    Imasked = I * mask
    mean = scipy.stats.nanmean(Imasked.flatten())
    std = scipy.stats.nanstd(Imasked.flatten())
    return mean, std

def experiment_vary_contrast(args):
    """ Investigates the affect of varying the contrast of INK-levels on
    accuracy.
    """
    testsetdir = args.testsetdir
    outpath = args.out
    align_strat = args.align_strat
    debug = args.debug
    N = args.n

    ALPHA_LOW, ALPHA_HIGH, ALPHA_STEP = args.vary_contrast

    if ALPHA_LOW == ALPHA_HIGH:
        ALPHAS = [ALPHA_LOW]
    else:
        ALPHAS = np.linspace(ALPHA_LOW, ALPHA_HIGH, num=math.ceil((ALPHA_HIGH-ALPHA_LOW)/ALPHA_STEP), endpoint=True)
    alpha2Ps = {}
    alpha2L1norms, alpha2xerrs, alpha2yerrs, alpha2terrs = {}, {}, {}, {}
    alpha2inkstats = {} # maps {float ALPHA: [(I_inkmean, I_inkstd, Iref_inkmean, Iref_inkstd), ...]}
    t_total = time.time()
    for i, alpha in enumerate(ALPHAS):
        print "({0}/{1}) Evaluating with alpha={2:.3f}".format(i+1, len(ALPHAS), alpha)
        t = time.time()
        errs_map, errs, errs_x, errs_y, errs_theta, dur, userdata = eval_testset(testsetdir, align_strat=align_strat,
                                                                                 debug=debug, NUM_BALLOTS=N,
                                                                                 CONTRAST_ALPHA=alpha,
                                                                                 show_overlays_interactive=args.interactive)
        dur = time.time() - t
        print "Finished iter {0}/{1} ({2:.4f}s)".format(i+1, len(ALPHAS), dur)
        alpha2L1norms[alpha] = errs
        alpha2xerrs[alpha] = np.abs(errs_x)
        alpha2yerrs[alpha] = np.abs(errs_y)
        alpha2terrs[alpha] = np.abs(errs_theta)
        alpha2inkstats[alpha] = userdata['inkstats']
        for (srcpath, dstpath), (P_expected, P_found) in errs_map.iteritems():
            alpha2Ps.setdefault(alpha, []).append((P_expected, P_found))
    dur_total = time.time() - t_total
    print "Done. ({0:.4f}s)".format(dur_total)

    def get_nums():
        src2dsts = pickle.load(open(os.path.join(testsetdir, 'src2dsts.p')))
        num_ballots = args.n if args.n != None else len(src2dsts)
        num_alignments = num_ballots * len(src2dsts[src2dsts.keys()[0]])
        return num_ballots, num_alignments

    num_ballots, num_alignments = get_nums()

    fig0 = plt.figure()
    fig0.suptitle("Experiment: VaryContrast (testsetdir={0}, align_strat={1}, num_ballots={2}, num_alignments={3})".format(testsetdir, align_strat, num_ballots, num_alignments))

    plot_xerrs = fig0.add_subplot(321)
    plot_xerrs.set_title("ALPHA vs. Abs X Errors")
    plot_xerrs.set_xlabel("ALPHA value")
    plot_xerrs.set_ylabel("X Error (pixels)")
    plot_errorbars(alpha2xerrs, plot_xerrs)

    plot_yerrs = fig0.add_subplot(322)
    plot_yerrs.set_title("ALPHA vs. Abs Y Errors")
    plot_yerrs.set_xlabel("Alpha value")
    plot_yerrs.set_ylabel("Y Error (pixels)")
    plot_errorbars(alpha2yerrs, plot_yerrs)

    plot_terrs = fig0.add_subplot(323)
    plot_terrs.set_title("ALPHA vs. Abs Theta Errors")
    plot_terrs.set_xlabel("Alpha value")
    plot_terrs.set_ylabel("Theta Error (degrees)")
    plot_errorbars(alpha2terrs, plot_terrs)

    plot_L1norms = fig0.add_subplot(324)
    plot_L1norms.set_title("ALPHA vs. L1 norms")
    plot_L1norms.set_xlabel("Alpha value")
    plot_L1norms.set_ylabel("L1 norm")
    plot_errorbars(alpha2L1norms, plot_L1norms)

    alpha2inkmeandiffs = {}
    for alpha, inkstats in alpha2inkstats.iteritems():
        mean_diffs = []
        for (I_inkmean, I_inkstd, Iref_inkmean, Iref_inkstd) in inkstats:
            mean_diffs.append(Iref_inkmean - I_inkmean)
        alpha2inkmeandiffs[alpha] = mean_diffs

    plot_inkstats = fig0.add_subplot(325)
    plot_inkstats.set_title("ALPHA vs. Ink-Darkness Diff. btwn. I, Iref.")
    plot_inkstats.set_xlabel("Alpha")
    plot_inkstats.set_ylabel("Mean Error")
    plot_errorbars(alpha2inkmeandiffs, plot_inkstats)

    fig0.show()
    
    pdb.set_trace()

def experiment_vary_contrast_patches(args):
    """ Investigates affect of adjusting the contrast of a random set of
    patches. I prefer the other vary_contrast experiment.
    """
    testsetdir = args.testsetdir
    outpath = args.out
    align_strat = args.align_strat
    debug = args.debug
    N = args.n

    C_N, C_W, C_H, C_ALPHA_LOW, C_ALPHA_HIGH, C_ALPHA_STEP = args.vary_contrast_patches
    def parse_contrastbboxes():
        if not args.contrastbboxes:
            return None
        nums = [int(coord) for coord in args.contrastbboxes]
        bboxes = []
        curbox = []
        for i, coord in enumerate(nums):
            if i % 4 == 0 and i != 0:
                bboxes.append(curbox)
                curbox = []
            curbox.append(coord)
        bboxes.append(curbox)
        return bboxes
    
    contrast_bboxes = parse_contrastbboxes()
    if C_ALPHA_LOW == C_ALPHA_HIGH:
        ALPHAS = [C_ALPHA_LOW]
    else:
        ALPHAS = np.linspace(C_ALPHA_LOW, C_ALPHA_HIGH, num=math.ceil((C_ALPHA_HIGH-C_ALPHA_LOW)/C_ALPHA_STEP), endpoint=True)
    alpha2Ps = {}
    alpha2L1norms, alpha2xerrs, alpha2yerrs, alpha2terrs = {}, {}, {}, {}
    t_total = time.time()
    for i, alpha in enumerate(ALPHAS):
        print "({0}/{1}) Evaluating with alpha={2:.3f}".format(i+1, len(ALPHAS), alpha)
        t = time.time()
        errs_map, errs, errs_x, errs_y, errs_theta, dur, _ = eval_testset(testsetdir, align_strat=align_strat,
                                                                          debug=debug, NUM_BALLOTS=N,
                                                                          CONTRAST_NUM=C_N, CONTRAST_W=C_W, CONTRAST_H=C_H, CONTRAST_ALPHA=alpha,
                                                                          CONTRAST_BBOXES=contrast_bboxes,
                                                                          show_overlays_interactive=args.interactive)
        dur = time.time() - t
        print "Finished iter {0}/{1} ({2:.4f}s)".format(i+1, len(ALPHAS), dur)
        alpha2L1norms[alpha] = errs
        alpha2xerrs[alpha] = np.abs(errs_x)
        alpha2yerrs[alpha] = np.abs(errs_y)
        alpha2terrs[alpha] = np.abs(errs_theta)
        for (srcpath, dstpath), (P_expected, P_found) in errs_map.iteritems():
            alpha2Ps.setdefault(alpha, []).append((P_expected, P_found))
    dur_total = time.time() - t_total
    print "Done. ({0:.4f}s)".format(dur_total)

    def get_nums():
        src2dsts = pickle.load(open(os.path.join(testsetdir, 'src2dsts.p')))
        num_ballots = args.n if args.n != None else len(src2dsts)
        num_alignments = num_ballots * len(src2dsts[src2dsts.keys()[0]])
        return num_ballots, num_alignments

    num_ballots, num_alignments = get_nums()

    fig0 = plt.figure()
    fig0.suptitle("Experiment: VaryContrastPatches (testsetdir={0}, align_strat={1}, num_ballots={2}, num_alignments={3})".format(testsetdir, align_strat, num_ballots, num_alignments))

    plot_xerrs = fig0.add_subplot(221)
    plot_xerrs.set_title("ALPHA vs. Abs X Errors")
    plot_xerrs.set_xlabel("ALPHA value")
    plot_xerrs.set_ylabel("X Error (pixels)")
    plot_errorbars(alpha2xerrs, plot_xerrs)

    plot_yerrs = fig0.add_subplot(222)
    plot_yerrs.set_title("ALPHA vs. Abs Y Errors")
    plot_yerrs.set_xlabel("Alpha value")
    plot_yerrs.set_ylabel("Y Error (pixels)")
    plot_errorbars(alpha2yerrs, plot_yerrs)

    plot_terrs = fig0.add_subplot(223)
    plot_terrs.set_title("ALPHA vs. Abs Theta Errors")
    plot_terrs.set_xlabel("Alpha value")
    plot_terrs.set_ylabel("Theta Error (degrees)")
    plot_errorbars(alpha2terrs, plot_terrs)

    plot_L1norms = fig0.add_subplot(224)
    plot_L1norms.set_title("ALPHA vs. L1 norms")
    plot_L1norms.set_xlabel("Alpha value")
    plot_L1norms.set_ylabel("L1 norm")
    plot_errorbars(alpha2L1norms, plot_L1norms)

    fig0.show()
    
    pdb.set_trace()

def plot_errorbars(x2ys, plot):
    """ Plots error bars with given data X2YS.
    http://ww1.cpa-apc.org:8080/publications/archives/PDF/1996/Oct/strein2.pdf
    Input:
        dict X2YS: maps {x: [y0, y1, ...]}
    Output:
        The plot object.
    """
    xs_, ys_ = [], []
    CIs = []
    for x, ys in sorted(x2ys.iteritems(), key=lambda t: t[0]):
        mean, std = np.mean(ys), np.std(ys)
        SE = std / math.sqrt(len(ys)) # Standard Error
        CIs.append(1.96 * SE) # 95% confidence
        xs_.append(x); ys_.append(mean)
    plot.errorbar(xs_, ys_, yerr=CIs, fmt='ro')
    return plot

def experiment_alt_refimg(args):
    """ Aligns each image in the testset to alternate reference images (rather
    than to the ground-truth ref image. Compares to aligning against the ground-truth
    refimg.
    """
    testsetdir = args.testsetdir
    outpath = args.out
    align_strat = args.align_strat
    debug = args.debug
    N = args.n

    if align_strat != STRAT_LK:
        print "(Error) Must use align_strat=align_lk (passed in:)", align_strat
        return

    def get_nums():
        src2dsts = pickle.load(open(os.path.join(testsetdir, 'src2dsts.p')))
        num_ballots = args.n if args.n != None else len(src2dsts)
        num_alignments = num_ballots * len(src2dsts[src2dsts.keys()[0]])
        return num_ballots, num_alignments
    def get_refimgpaths(alt_refimgsdir):
        imgpaths_out = []
        if not os.path.isdir(alt_refimgsdir):
            return [alt_refimgsdir]
        for dirpath, dirnames, filenames in os.walk(alt_refimgsdir):
            for imgname in [f for f in filenames if f.lower().endswith('.png')]:
                imgpaths_out.append(os.path.join(dirpath, imgname))
        return imgpaths_out

    num_ballots, num_alignments = get_nums()

    alt_refimgsdir = args.alt_refimg
    alt_refimgpaths = get_refimgpaths(alt_refimgsdir)
    ref2xerrs, ref2yerrs, ref2terrs, ref2L1norms = {}, {}, {}, {}
    t_total = time.time()
    for i, refimgpath in enumerate(sorted(alt_refimgpaths)):
        print "({0}/{1}) Trying refimg={2}".format(i+1, len(alt_refimgpaths), refimgpath)
        t = time.time()
        
        errs_map, errs, errs_x, errs_y, errs_theta, dur, userdata = eval_testset(testsetdir, align_strat=align_strat,
                                                                                 debug=debug, NUM_BALLOTS=N,
                                                                                 alt_refimgpath=refimgpath,
                                                                                 minArea=np.power(2, 14),
                                                                                 show_overlays_interactive=args.interactive)
        ref2xerrs[refimgpath] = np.abs(errs_x)
        ref2yerrs[refimgpath] = np.abs(errs_y)
        ref2terrs[refimgpath] = np.abs(errs_theta)
        ref2L1norms[refimgpath] = errs

        dur = time.time() -t
        print "Done with iter {0}/{1} ({2:.4f}s)".format(i+1, len(alt_refimgpaths), dur)

    fig0 = plt.figure()
    fig0.suptitle("Experiment: Alt. Refimgs. (testset={0} align_strat={1} numBallots={2} numAligns={3})".format(testsetdir, align_strat, num_ballots, num_alignments))

    refpath2refname = {}
    for refimgpath in alt_refimgpaths:
        refpath2refname[refimgpath] = os.path.split(refimgpath)[1]

    plot_xerrs = fig0.add_subplot(221)
    plot_xerrs.set_title("Abs. X Error Histogram across refimgs")
    plot_xerrs.set_xlabel("Abs. X Error (pixels)")
    plot_stacked_hists(ref2xerrs, plot_xerrs, labels=refpath2refname)

    plot_yerrs = fig0.add_subplot(222)
    plot_yerrs.set_title("Abs. Y Error Histogram across refimgs")
    plot_yerrs.set_xlabel("Abs. Y Error (pixels)")
    plot_stacked_hists(ref2yerrs, plot_yerrs, labels=refpath2refname)

    plot_terrs = fig0.add_subplot(223)
    plot_terrs.set_title("Abs. Theta Error Histogram across refimgs")
    plot_terrs.set_xlabel("Abs Theta Error (degrees)")
    plot_stacked_hists(ref2terrs, plot_terrs, labels=refpath2refname)

    plot_L1norms = fig0.add_subplot(224)
    plot_L1norms.set_title("L1 norms (btwn Ireg, Iref) Histogram across refimgs")
    plot_L1norms.set_xlabel("L1 norm (ranges from [0.0, 1.0])")
    plot_stacked_hists(ref2L1norms, plot_L1norms, labels=refpath2refname)

    dur_total = time.time() - t_total
    print "Done ({0:.4f}s total)".format(dur_total)

    fig0.show()

    pdb.set_trace()

def experiment_vary_minarea(args):
    """ Investigate the affect of varying the minarea parameter, i.e. how much
    to lean on the pyramid optimization.
    """
    testsetdir = args.testsetdir
    outpath = args.out
    align_strat = args.align_strat
    interactive_overlays = args.interactive
    debug = args.debug
    N = args.n

    if args.minarea != None:
        k_low, k_high, k_step = args.minarea
        refimgpath = None
    else:
        k_low, k_high, k_step, refimgpath = args.minarea_refimg
        k_low, k_high, k_step = float(k_low), float(k_high), float(k_step)
        print "Using alternate refimg={0}".format(refimgpath)

    ks = np.linspace(k_low, k_high, num=math.ceil((k_high - k_low) / k_step), endpoint=True)
    
    t_total = time.time()
    k2xerrs, k2yerrs, k2terrs, k2L1norms = {}, {}, {}, {}
    for i, k in enumerate(ks):
        minArea = np.power(2, k)
        print "({0}/{1}) Running with minArea={2}".format(i+1, len(ks), minArea)
        t = time.time()
        errs_map, errs, errs_x, errs_y, errs_theta, dur, userdata = eval_testset(testsetdir, align_strat=align_strat,
                                                                                 debug=debug, NUM_BALLOTS=N,
                                                                                 minArea=minArea,
                                                                                 alt_refimgpath=refimgpath,
                                                                                 show_overlays_interactive=args.interactive)
        k2xerrs[k] = np.abs(errs_x)
        k2yerrs[k] = np.abs(errs_y)
        k2terrs[k] = np.abs(errs_theta)
        k2L1norms[k] = errs
        dur = time.time() - t
        print "Iter Finished ({0:.4f}s) ({1}/{2})".format(dur, i+1, len(ks))

    dur_total = time.time() - t_total

    def get_nums():
        src2dsts = pickle.load(open(os.path.join(testsetdir, 'src2dsts.p')))
        num_ballots = args.n if args.n != None else len(src2dsts)
        num_alignments = num_ballots * len(src2dsts[src2dsts.keys()[0]])
        return num_ballots, num_alignments
    num_ballots, num_alignments = get_nums()

    print "Done. ({0:.4f}s)".format(dur_total)

    fig0 = plt.figure()
    fig0.suptitle("Experiment: varyMinArea. (testset={0} align_strat={1} numBallots={2} numAligns={3})".format(testsetdir, align_strat, num_ballots, num_alignments))

    plot_xerrs = fig0.add_subplot(221)
    plot_xerrs.set_title("Abs. X Error across K (minArea := 2**K)")
    plot_xerrs.set_xlabel("K")
    plot_xerrs.set_ylabel("Abs. X Error (Pixels)")
    plot_errorbars(k2xerrs, plot_xerrs)

    plot_yerrs = fig0.add_subplot(222)
    plot_yerrs.set_title("Abs. Y Error across K (minArea := 2**K)")
    plot_yerrs.set_xlabel("K")
    plot_yerrs.set_ylabel("Abs. Y Error (pixels)")
    plot_errorbars(k2yerrs, plot_yerrs)

    plot_terrs = fig0.add_subplot(223)
    plot_terrs.set_title("Abs. Theta Error across K (minArea := 2**K)")
    plot_terrs.set_xlabel("K")
    plot_terrs.set_ylabel("Abs Theta Error (degrees)")
    plot_errorbars(k2terrs, plot_terrs)

    plot_L1norms = fig0.add_subplot(224)
    plot_L1norms.set_title("L1 norms across K (minArea := 2**K)")
    plot_L1norms.set_xlabel("K")
    plot_L1norms.set_ylabel("L1 norm (ranges from [0.0, 1.0])")
    plot_errorbars(k2L1norms, plot_L1norms)

    fig0.show()

    pdb.set_trace()

def plot_stacked_hists(x2data, plot, labels=None):
    """ For each set of (x->DATA) in X2DATA, plot each DATA histogram onto
    PLOT, with different colors.
    Input:
        dict LABELS: {X: str label}
    """
    COLORS = ("b", "g", "r", "c", "m", "y")
    bars = [] # [(x, Plot bar), ...]
    width = 0.0
    for _, data in x2data.iteritems():
        hist, bins = np.histogram(data, bins=50)
        width = max(width, 0.7 * (bins[1] - bins[0]))
    for i, (x, data) in enumerate(sorted(x2data.iteritems())):
        COLOR = COLORS[i % len(COLORS)]
        bar = plot_hist(data, plot, color=COLOR, alpha=0.5, width=width)
        hist, bins = np.histogram(data, bins=50)
        plot.axvline(x=bins[0], color=COLOR)
        plot.axvline(x=bins[-1], color=COLOR)
        bars.append((x, bar))
    if labels != None:
        plot.legend([tup[1][0] for tup in bars], [labels[x] for (x,bar) in bars])
    return plot

def parse_args():
    parser = argparse.ArgumentParser(description=DESCRIPTION)
    ## Positional Arguments
    parser.add_argument("testsetdir", help="Testset location (from the \
'create_testset.py' script).")
    ## Optional Arguments
    parser.add_argument("--out", help="Output path to store results as \
a pickle'd file. (Suggested: <testsetdir>/out_eval_align.p)")
    parser.add_argument("--align_strat", help="Alignment strategy to use. \
Default: align_lk",
                        choices=(STRAT_CV, STRAT_LK, TRY_ALL_STRATS),
                        default=STRAT_LK)
    parser.add_argument("--interactive", help="After each alignment, display the \
resulting images+overlays, and wait for the user to hit enter. Default: False",
                        action="store_true", default=False)
    parser.add_argument("--debug", help="Enable debugging output. Default: False",
                        action="store_true", default=False)
    parser.add_argument("--n", help="Only evaluate first N ballots.",
                        type=int)
    parser.add_argument("--restore", help="Read-in a previously-generated pickle'd \
results file, and re-plot the data.")

    ## align_lk specific 
    parser.add_argument("--crop", help="(LK) Evaluate align_lk on a range of X/Y crop values. \
Should be percentages of the image width/height, e.g. --crop 0.10 0.02 0.15 0.05. If the STEP \
are 0, then use only a fixed-size crop param, e.g. --crop 0.02 0 0.02 0. Default: (0.02 0 0.02 0).",
                        nargs=4, type=float, metavar=("XMAX", "XSTEP", "YMAX", "YSTEP"),
                        default=(0.02, 0, 0.02, 0))
    parser.add_argument("--crop_box", help="(LK) Like --crop, but both CROPX/CROPY are the same. \
Overrides --crop if this is present.",
                        nargs=2, type=float, metavar=("CROPMAX", "CROPSTEP"))

    parser.add_argument("--rszFacs", help="(LK) Evaluate align_lk on a range of initial \
rescaling amounts. Should be percentages, e.g. --rszFacs 0.05 0.15 0.05. \
If STEP or HIGH is 0, then use a fixed-size rescale factor. Default: (0.15 0 0).",
                        nargs=3, type=float, metavar=("LOW", "HIGH", "STEP"),
                        default=(0.15, 0, 0))

    parser.add_argument("--vary_contrast", help="Investigate effect of increasing/lowering \
the contrast of ink on ballots. ALPHA is the amount by which to multiply intensity values by.",
                         nargs=3, metavar=("ALPHA_LOW", "ALPHA_HIGH", "ALPHA_STEP"),
                         type=float)

    parser.add_argument("--vary_contrast_patches", help="Investigate affect of increasing/lowering \
the contrast of N patches of size WxH, randomly placed, by a factor of ALPHA. Runs a separate \
experiment.",
                        metavar=("N", "W", "H", "ALPHA_LOW", "ALPHA_HIGH", "ALPHA_STEP"),
                        nargs=6,
                        type=float)
    parser.add_argument("--contrastbboxes", help="Specify hardcoded boundingboxes, e.g. \
--contrastbboxes X1 Y1 X2 Y2 [X1 Y2 X2 Y2]*. You must still pass in --vary_contrast_patches, but \
the N,W,H values don't matter. This overrides N,W,H.",
                        nargs='+')

    parser.add_argument("--alt_refimg", help="Use alternate reference images in IREFDIR. \
For sensible results, each SRCIMG in the testset must already be aligned to each image in \
IREFDIR (each image in IREFDIR must also be aligned to each other). IREFDIR may also point \
to a single refimg.",
                        metavar="IREFDIR")

    parser.add_argument("--minarea", help="Investigate effect of increasing the minArea \
parameter of imagesAlign, which controls the pyramid optimization. Input ints are used as \
the exponent in: minArea = 2 ** K. ",
                        metavar=("K_LOW", "K_HIGH", "K_STEP"), nargs=3, type=float)

    parser.add_argument("--minarea_refimg", help="Run the minarea experiment, but with \
using a different refimg.",
                        metavar=("K_LOW", "K_HIGH", "K_STEP", "IREF"), nargs=4)

    args = parser.parse_args()
    return args

def main():
    args = parse_args()

    testsetdir = args.testsetdir
    outpath = args.out
    align_strat = args.align_strat
    interactive_overlays = args.interactive
    debug = args.debug
    N = args.n

    if align_strat == TRY_ALL_STRATS:
        return experiment_compare_align_strats(args)

    if args.crop[1] != 0 or args.crop_box != None:
        return experiment_vary_crop(args)
    elif args.vary_contrast_patches != None:
        return experiment_vary_contrast_patches(args)
    elif args.vary_contrast != None:
        return experiment_vary_contrast(args)
    elif args.alt_refimg != None:
        return experiment_alt_refimg(args)
    elif args.minarea != None or args.minarea_refimg != None:
        return experiment_vary_minarea(args)
    elif not args.restore:
        print "...Evaluating the testset at: {0} (with align_strat={1})".format(testsetdir, align_strat)
        cropx, _, cropy, _ = args.crop
        # dict errs_map: maps {(srcpath, dstpath): (P_expected, P_found)}
        errs_map, errs, errs_x, errs_y, errs_theta, dur, _ = eval_testset(testsetdir, align_strat=align_strat,
                                                                          debug=debug, NUM_BALLOTS=N,
                                                                          cropx=cropx, cropy=cropy,
                                                                          show_overlays_interactive=interactive_overlays)
    else:
        restore_path = args.restore
        print "(Info) Loading in previous results file: {0}".format(restore_path)
        _, _, (errs_map, errs, errs_x, errs_y, errs_theta, dur) = pickle.load(open(restore_path, 'rb'))
    print "...Done Evaluating ({0} secs)".format(dur)
    print "    Average per Alignment: {0} secs".format(dur / float(len(errs)))
    print
    print "(Pixel Error) Mean={0}    Std={1}    ({2} total alignments)".format(np.mean(errs), np.std(errs), len(errs))
    print "(X Error) Mean={0}    Std={1}".format(np.mean(errs_x), np.std(errs_x))
    print "(Y Error) Mean={0}    Std={1}".format(np.mean(errs_y), np.std(errs_y))
    print "(Theta Error) Mean={0}    Std={1}".format(np.mean(errs_theta), np.std(errs_theta))
    
    if outpath:
        outinfo = (testsetdir, align_strat, (errs_map, errs, errs_x, errs_y, errs_theta, dur))
        print "(Info) Saving eval info to: {0}".format(outpath)
        pickle.dump(outinfo, open(outpath, 'wb'))

    plot_errs(errs_map, errs, errs_x, errs_y, errs_theta)

    pdb.set_trace()

    print "Done."

if __name__ == '__main__':
    main()
