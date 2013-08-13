import sys, os, pdb, argparse
import numpy as np, cv2, cv
import time

from os.path import join as pathjoin

import scipy, scipy.misc, scipy.linalg, numpy as np

sys.path.append('..')
import pixel_reg.imagesAlign as imagesAlign
import pixel_reg.shared as sh

try: 
    import matplotlib.pyplot as plt
except:
    print "Couldn't import matplotlib. Can't plot."

"""
Functions that globally-align ballot images together.
"""

USAGE = """Usage:
    python global_align.py [-h --help -help] [--num N] [--verbose] 
                           [--method METHOD] [--save_overlays]
                           IMGPATHS REF_IMGPATH OUTDIR

Aligns all images in IMGPATHS to REF_IMGPATH, and stores registered images
to OUTDIR.

--method METHOD [Default=normal]
    Which alignment strategy to use. One of:
        normal, cvrigid
--save_overlays
    If given, then this will save the overlay of each IREG and IREF to OUTDIR.
    Else, this will save just the aligned IREG to OUTDIR.
"""

ALIGN_NORMAL = 'normal'
ALIGN_CVRIGID = 'cvrigid'

def align_image(I, Iref, crop=True, verbose=False,
                CROPX=0.02, CROPY=0.02, ERR_REL_THR=1.001,
                RSZFAC=0.15, MINAREA=None):
    """ Aligns I to IREF (e.g. 'global' alignment). Both IREF and I
    must be correctly 'flipped' before you pass it to this function.
    Input:
        nparray IREF
    The reference image that we are aligning against.
        nparray I
    The image that we want to align.
        float CROPX, CROPY, OR tuple CROPX, tuple CROPY
    The amount to crop off the top+bottom and left+right of the image (used
    with CROP=True). 
    If CROPX, CROPY are tuples, they must be the same length, and we will
    try all sequential pairs until we get a relative error that is <= ERR_REL_THR. 
    If none are <= ERR_REL_THR, then we output the alignment with smallest error.
        float ERR_REL_THR
    See the docstring for the tuple-version of CROPX, CROPY.
        int MINAREA
    This parameter dictates how "far down" the pyramid optimization should
    downscale the image. For instance, if MINAREA is K, then a new pyramid
    level will be created by downscaling the image by a factor of 2.0 until
    the image area is <= K. 
    Larger values of MINAREA mean that alignment is done at larger scales,
    which will lead to better accuracy, but may take more time. Smaller
    values of MINAREA incur better speedsup, but potentially at the cost
    of accuracy. The default value 2**16 is a reasonable value for accuracy.
    Output:
        (nparray H, nparray IREG, float err)
    where H is the transformation matrix, IREG is the result of aligning
    I to IREF, and ERR is the alignment error (a float from [0.0, 1.0]).
    """
    if MINAREA == None:
        MINAREA = np.power(2, 16)
    if crop and type(CROPX) in (list, tuple):
        return _align_image_mult(I, Iref, CROPX, CROPY, ERR_REL_THR)

    if crop == True:
        Iref_crop = cropout_stuff(Iref, CROPY, CROPY, CROPX, CROPX)
        Icrop = cropout_stuff(I, CROPY, CROPY, CROPX, CROPX)
    else:
        Icrop, Iref_crop = I, Iref

    H, err = imagesAlign.imagesAlign(Icrop, Iref_crop, trfm_type='rigid', rszFac=RSZFAC, applyWarp=False, minArea=MINAREA)
    if verbose:
        print "Alignment Err: ", err
    Ireg = sh.imtransform(I, H)
    #Ireg = np.nan_to_num(Ireg)
    return H, Ireg, err

def _align_image_mult(I, Iref, CROPX, CROPY, ERR_REL_THR):
    """ Helper function for align_image. Handles trying multiple crop
    parameters until an err_rel is found that is <= ERR_REL_THR.
    """
    best_H, best_Ireg, best_err = None, None, None
    err_orig = np.mean(np.abs(I - Iref).flatten()) # L1 error, normalized by area
    for i, cropx in enumerate(CROPX):
        cropy = CROPY[i]
        I_crop = cropout_stuff(I, cropy, cropy, cropx, cropx)
        Iref_crop = cropout_stuff(Iref, cropy, cropy, cropx, cropx)
        H, err = imagesAlign.imagesAlign(I_crop, Iref_crop, trfm_type='rigid', rszFac=0.15, applyWarp=False)
        Ireg = sh.imtransform(I, H)
        err_galign = np.mean(np.abs(Ireg - Iref).flatten())
        err_rel = err_galign / err_orig if err_orig != 0.0 else 0.0
        if err_rel <= ERR_REL_THR:
            return H, Ireg, err_galign
        elif best_H == None or err_galign < best_err:
            best_H, best_Ireg, best_err = H, Ireg, err_galign
    return best_H, best_Ireg, best_err

def cropout_stuff(I, top, bot, left, right):
    """ Crops out some percentage from each side of I. """
    h, w = I.shape
    x1 = int(round(left*w))
    y1 = int(round(top*h))
    x2 = int(round(w - (right*w)))
    y2 = int(round(h - (bot*h)))
    Inew = I[y1:y2, x1:x2]
    return np.copy(Inew)

def correctH(I, H0):
    """ Given an image I and its transformation matrix H0 which is wrt
    the image origin, output a new transformation matrix H that is in
    the image coordinate system of I.
    """
    T0=np.eye(3); T0[0,2]=I.shape[1]/2.0; T0[1,2]=I.shape[0]/2.0
    T1=np.eye(3); T1[0,2]=-I.shape[1]/2.0; T1[1,2]=-I.shape[0]/2.0
    H=np.dot(np.dot(T0,H0),T1)
    return H

def align_strong(I, Iref, scales=(0.15, 0.2, 0.25, 0.3), 
                 crop_I=(0.05, 0.05, 0.05, 0.05), 
                 crop_Iref=None, do_nan_to_num=False):
    """ Alignment strategy: First, crop out 5% from each side of I.
    Then, try a range of scales, and choose the alignment that 
    minimizes the error.
    CURRENTLY NOT USED.
    """
    if crop_I != None:
        Icrop = cropout_stuff(I, crop_I[0], crop_I[1], crop_I[2], crop_I[3])
    else:
        Icrop = I
    if crop_Iref != None:
        Iref_crop = cropout_stuff(Iref, crop_Iref[0], crop_Iref[1], crop_Iref[2], crop_Iref[3])
    else:
        Iref_crop = Iref
    H_best, Ireg_best, err_best = None, None, None
    scale_best = None
    for scale in scales:
        H, Ireg, err = imagesAlign.imagesAlign(Icrop, Iref_crop, fillval=1, trfm_type='rigid', rszFac=scale)
        if err_best == None or err < err_best:
            H_best = H
            Ireg_best = Ireg
            err_best = err
            scale_best = scale
    # Finally, apply H_BEST to I
    Ireg = sh.imtransform(I, H_best)
    if do_nan_to_num:
        Ireg = np.nan_to_num(Ireg)
    return H_best, Ireg, err_best

def align_cv(I_in, Iref_in, fullAffine=False, resizeDims=None, computeErr=False,
             crop=None, rmBlkBorder=True, doSmooth=False, smooth_sigma=12):
    """ Aligns I to IREF, assuming an affine model. If FULLAFFINE is
    True, then estimate a true affine transform (6 degrees of
    freedom). Otherwise, limit to translation, rotation, scaling (5
    degrees of freedom).
    Input:
        nparray I, nparray IREF: Must be uint8 dtype, same size.
        bool FULLAFFINE:
        tuple resizeDims: (int MAXDIM, int MINDIM)
            If necessary, resize I, IREF s.t. its largest dimension is
            MINDIM <= MAXDIM. (Put None for MINDIM if you don't care).
        bool COMPUTEERR:
            If True, then this estimate the alignment error by doing a
            pixel-diff between IREG and IREF. O.w. simply outputs None as err.
        tuple CROP: (float XAMT, float YAMT)
            If given, then this will remove a fractional amount from the
            edges of both I and IREF. e.g. crop=(0.02, 0.04) removes 2% of
            both left/right side, and 4% of the top/bottom sides.
        bool RMBLKBORDER:
            If True, then this will ignore any possible black borders
            (that the straightener introduces) when doing alignment. This
            operation is done /before/ CROP is considered.
    Output:
        (nparray H, nparray IREG, float ERR).
    """
    if rmBlkBorder:
        I_topblk, I_botblk, I_leftblk, I_rightblk = compute_border(I_in)
        Iref_topblk, Iref_botblk, Iref_leftblk, Iref_rightblk = compute_border(Iref_in)
        i1, i2 = max(I_topblk, Iref_topblk), max(I_in.shape[0] - I_botblk, Iref_in.shape[0] - Iref_botblk)
        j1, j2 = max(I_leftblk, Iref_leftblk), max(I_in.shape[1] - I_rightblk, Iref_in.shape[1] - Iref_rightblk)
        I = I_in[i1:i2, j1:j2]
        Iref = Iref_in[i1:i2, j1:j2]
    else:
        I_topblk, I_botblk, I_leftblk, I_rightblk = 0, I_in.shape[0], 0, I_in.shape[1]
        Iref_topblk, Iref_botblk, Iref_leftblk, Iref_rightblk = 0, Iref_in.shape[0], 0, Iref_in.shape[1]
        I = I_in
        Iref = Iref_in
    if crop:
        Iref = cropout_stuff(Iref, crop[1], crop[1], crop[0], crop[0])
        I = cropout_stuff(I, crop[1], crop[1], crop[0], crop[0])

    if resizeDims:
        C = calc_rszFac((I.shape[1], I.shape[0]), resizeDims[0], resizeDims[1])
        I_rsz = sh.fastResize(I, C)
        Iref_rsz = sh.fastResize(I, C)
    else:
        I_rsz, Iref_rsz = I, Iref
    if doSmooth:
        #I_rsz = scipy.ndimage.filters.gaussian_filter(I_rsz, smooth_sigma, mode='nearest')
        #Iref_rsz = scipy.ndimage.filters.gaussian_filter(Iref_rsz, smooth_sigma, mode='nearest')
        I_rsz = cv2.GaussianBlur(I_rsz, (0,0), smooth_sigma)
        Iref_rsz = cv2.GaussianBlur(Iref_rsz, (0,0), smooth_sigma)

    H = cv2.estimateRigidTransform(I_rsz, Iref_rsz, fullAffine)
    try:
        H_ = np.eye(3, dtype=H.dtype)
        H_[:2,:] = H
        Hinv = scipy.linalg.inv(H_)
    except (np.linalg.linalg.LinAlgError, ValueError) as e:
        # In rare cases, H is singular (due to OpenCV bug?), thus outputting
        # bogus results.
        # Try aligning Iref to I, then invert the resultant H to get the
        # actual I->Iref transform.
        #print "SINGULAR MATRIX! Trying to align Ireg to I. ({0})".format(e.message)
        H_ = cv2.estimateRigidTransform(Iref_rsz, I_rsz, fullAffine)
        if np.any(np.isnan(H_)) or np.any(np.isinf(H_)):
            H = np.eye(3, dtype=H_.dtype)[:2,:]
        else:
            H_sq = np.eye(3, dtype=H_.dtype)
            H_sq[:2,:] = H_
            try:
                H = scipy.linalg.inv(H_sq)[:2,:]
            except np.linalg.linalg.LinAlgError as e:
                #print "SINGULAR MATRIX AGAIN! Uhoh. Outputting Identity mat."
                H = np.eye(3, dtype=H.dtype)[:2,:]

    Ireg = cv2.warpAffine(I_in, H, (I_in.shape[1], I_in.shape[0]))
    if not computeErr:
        err = None
    else:
        err = (np.sum(np.abs(Ireg - Iref_in)) / float(Ireg.shape[0] * Ireg.shape[1])) / 255.0
    return H, Ireg, err

def compute_border(A):
    """ Determines if the image contains rows/cols that are all black
    (e.g. introduced by the straightener).
    Output:
        (int top, int bottom, int left, int right).
    Where TOP is # of rows from top that are all black, BOT is # of
    rows from bottom that are all black, etc.
    """
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

def calc_rszFac(imgsize, maxdim, mindim):
    """ Outputs an appropriate scaling factor C s.t. the resultant
    image dimensions satisfy the constraint that the max dimension is
    MAXDIM, and dimensions are greater than MINDIM. MINDIM may be None
    if you don't care.
    """
    if imgsize[0] <= maxdim and imgsize[1] <= maxdim:
        return 1.0
    C = float(maxdim) / max(imgsize)
    if mindim != None and min(C * imgsize[0], C * imgsize[1]) < mindim:
        C = float(mindim) / min(imgsize)
    return C

def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("imgsdir",
                        help="Images to align.")
    parser.add_argument("refpath",
                        help="Path to reference image.")
    parser.add_argument("outdir",
                        help="Directory to store output registered images.")

    parser.add_argument("--num", type=int, help="Limit number of alignments \
to do.")
    parser.add_argument("--method", choices=(ALIGN_NORMAL, ALIGN_CVRIGID),
                        default=ALIGN_NORMAL,
                        help="Alignment method to use.")
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--save_overlays", action="store_true", 
                        help="Save Ireg overlayed with Iref to OUTDIR, not just \
Ireg.")
    
    parser.add_argument("--roi", nargs=4, type=int, metavar=("x1", "y1", "x2", "y2"),
                        help="Align only a subregion of both images .")

    return parser.parse_args()
    
def main():
    args = parse_args()

    N = args.num
    meth_align = args.method

    VERBOSE = args.verbose
    SAVE_OVERLAYS = args.save_overlays

    imgsdir = args.imgsdir
    ref_imgpath = args.refpath
    outdir = args.outdir

    if not os.path.exists(outdir):
        os.makedirs(outdir)

    def get_imagepaths(imgsdir):
        if not os.path.isdir(imgsdir):
            return [imgsdir]
        imgpaths = []
        _cnt = 0
        for dirpath, dirnames, filenames in os.walk(imgsdir):
            for imgname in [f for f in filenames if f.lower().endswith('.png')]:
                if N != None and _cnt >= N:
                    return imgpaths
                imgpath = pathjoin(dirpath, imgname)
                imgpaths.append(imgpath)
                _cnt += 1
        return imgpaths

    imgpaths = get_imagepaths(imgsdir)

    if meth_align == ALIGN_NORMAL:
        Iref = sh.standardImread_v2(ref_imgpath, flatten=True)
    elif meth_align == ALIGN_CVRIGID:
        Iref = fast_imread(ref_imgpath, flatten=True, dtype='uint8')

    if args.roi:
        x1, y1, x2, y2 = args.roi
        Iref = Iref[y1:y2, x1:x2]

    print "Aligning against {0} images...".format(len(imgpaths))
    t = time.time()
    errs, errs_map = [], {}
    errs_rel, errs_rel_map = [], {}
    for imgpath in imgpaths:
        imgname = os.path.split(imgpath)[1]
        if meth_align == ALIGN_NORMAL:
            I = sh.standardImread_v2(imgpath, flatten=True)
            if args.roi:
                x1, y1, x2, y2 = args.roi
                I = I[y1:y2, x1:x2]
            H, Ireg, err = align_image(I, Iref, verbose=VERBOSE, CROPX=0.07, CROPY=0.07, MINAREA=np.power(2, 16))
            err_orig = np.mean(np.abs(I - Iref).flatten())
            err_galign = np.mean(np.abs(Ireg - Iref).flatten())
            err_rel = err_galign / err_orig
        elif meth_align == ALIGN_CVRIGID:
            I = fast_imread(imgpath, flatten=True, dtype='uint8')
            if args.roi:
                x1, y1, x2, y2 = args.roi
                I = I[y1:y2, x1:x2]
            H, Ireg, err_galign = align_cv(I, Iref, computeErr=True, fullAffine=False,
                                    rmBlkBorder=True, doSmooth=True)
            err_orig = np.mean(np.abs(I - Iref))
            err_rel = err_galign / err_orig
        else:
            raise Exception("Unknown Alignment Method: {0}".format(meth_align))
        errs_map[imgname] = err_galign
        errs.append(err_galign)
        errs_rel.append(err_rel)
        errs_rel_map[imgname] = err_rel
        print "err_orig: {0}".format(err_orig)
        print "err_galign: {0}".format(err_galign)
        outpath = pathjoin(outdir, imgname)
        if SAVE_OVERLAYS:
            overlay = Ireg + Iref
            scipy.misc.imsave(outpath, overlay)
        else:
            scipy.misc.imsave(outpath, Ireg)

    dur = time.time() - t
    err_mean, err_std = np.mean(errs), np.std(errs)
    file_stats = open(pathjoin(outdir, 'stats'), 'w')
    print "Err_Mean: {0}".format(err_mean)
    print "Err_Std : {0}".format(err_std)

    print "ErrRel_Mean: {0}".format(np.mean(errs_rel))
    print "ErrRel_Std : {0}".format(np.std(errs_rel))

    print "Done ({0:.5f}s Total, {1:.8f}s per image)".format(dur,
                                                             dur / len(imgpaths))
    print >>file_stats, "Err_Mean: {0}".format(err_mean)
    print >>file_stats, "Err_Std : {0}".format(err_std)
    print >>file_stats, "ErrRel_Mean: {0}".format(np.mean(errs_rel))
    print >>file_stats, "ErrRel_Std : {0}".format(np.std(errs_rel))

    print >>file_stats, "Done ({0:.5f}s Total, {1:.8f}s per image)".format(dur,
                                                                           dur / len(imgpaths))
    file_stats.close()

    fig = plt.figure()
    p0 = fig.add_subplot(111)
    p0.set_title("Histogram of Reduction in error (aka Pre-align-error / Post-align-error).\n\
If >1.0, then alignment introduced more error.")
    p0.set_xlabel("Ratio of Pre-align-error / Post-align-error")
    p0.set_ylabel("Occurrences")

    hist, bins = np.histogram(errs_rel)
    width = 0.7 * (bins[1]-bins[0])
    center = (bins[:-1]+bins[1:]) / 2.0

    p0.bar(center, hist, align='center', width=width)

    fig.show()

    raw_input("Press (enter) to continue.")
    
def fast_imread(imgpath, flatten=True, dtype='uint8'):
    if flatten:
        Icv = cv.LoadImageM(imgpath, cv.CV_LOAD_IMAGE_GRAYSCALE)
    else:
        Icv = cv.LoadImageM(imgpath, cv.CV_LOAD_IMAGE_COLOR)
    Inp = np.asarray(Icv, dtype=dtype)
    return Inp

if __name__ == '__main__':
    main()
