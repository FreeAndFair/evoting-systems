import os, sys, time
import numpy as np, scipy.misc as misc, cv

sys.path.append('..')
import pixel_reg.imagesAlign as imagesAlign

def make_minmax_overlay(imgpaths, do_align=False, rszFac=1.0):
    overlayMin, overlayMax = None, None
    Iref = None
    for path in imgpaths:
        img = misc.imread(path, flatten=1)
        if do_align and Iref == None:
            Iref = img
        elif do_align:
            (H, img, err) = imagesAlign.imagesAlign(img, Iref, fillval=0, rszFac=rszFac)
        if (overlayMin == None):
            overlayMin = img
        else:
            if overlayMin.shape != img.shape:
                h, w = overlayMin.shape
                img = resize_img_norescale(img, (w,h))
            overlayMin = np.fmin(overlayMin, img)
        if (overlayMax == None):
            overlayMax = img
        else:
            if overlayMax.shape != img.shape:
                h, w = overlayMax.shape
                img = resize_img_norescale(img, (w,h))
            overlayMax = np.fmax(overlayMax, img)

    #rszFac=sh.resizeOrNot(overlayMax.shape,sh.MAX_PRECINCT_PATCH_DISPLAY)
    #overlayMax = sh.fastResize(overlayMax, rszFac) #/ 255.0
    #overlayMin = sh.fastResize(overlayMin, rszFac) #/ 255.0
    return overlayMin, overlayMax

def resize_img_norescale(img, size):
    """ Resizes img to be a given size without rescaling - it only
    pads/crops if necessary.
    Input:
        obj img: a numpy array
        tuple size: (w,h)
    Output:
        A numpy array with shape (h,w)
    """
    w,h = size
    shape = (h,w)
    out = np.zeros(shape)
    i = min(img.shape[0], out.shape[0])
    j = min(img.shape[1], out.shape[1])
    out[0:i,0:j] = img[0:i, 0:j]
    return out

def iplimage2np(img):
    a = np.frombuffer(img.tostring(), dtype=np.uint8)
    a.shape = img.height, img.width
    return a

def np2iplimage(array):
    img = cv.CreateImageHeader((array.shape[1], array.shape[0]), cv.IPL_DEPTH_8U, 1)
    cv.SetData(img, array.tostring(), array.dtype.itemsize * 1 * array.shape[1])
    return img

def overlay_minmax_cv(imgpaths, do_align=False, rszFac=1.0):
    imgpath = imgpaths[0]
    Imin = cv.LoadImage(imgpath, cv.CV_LOAD_IMAGE_GRAYSCALE)
    Imax = cv.CloneImage(Imin)
    #Iref = np.asarray(cv.CloneImage(Imin)) if do_align else None
    Iref = (iplimage2np(cv.CloneImage(Imin)) / 255.0) if do_align else None
    for imgpath in imgpaths[1:]:
        I = cv.LoadImage(imgpath, cv.CV_LOAD_IMAGE_GRAYSCALE)
        Iout = matchsize(I, Imax)
        if do_align:
            tmp_np = iplimage2np(cv.CloneImage(Iout)) / 255.0
            H, Ireg, err = imagesAlign.imagesAlign(tmp_np, Iref, fillval=0, rszFac=rszFac)
            Ireg *= 255.0
            Ireg = Ireg.astype('uint8')
            Iout = np2iplimage(Ireg)

        cv.Max(Iout, Imax, Imax)
        cv.Min(Iout, Imin, Imin)
    return Imin, Imax

def matchsize(A, B):
    if A.width == B.width and A.height == B.height:
        return A
    wA, hA = A.width, A.height
    SetImageROI = cv.SetImageROI
    out = cv.CreateImage((B.width, B.height), A.depth, A.channels)
    wOut, hOut = out.width, out.height
    if wA < wOut and hA < hOut:
        SetImageROI(out, (0, 0, wA, hA))
    elif wA >= wOut and hA < hOut:
        SetImageROI(out, (0, 0, wOut, hA))
        SetImageROI(A, (0, 0, wOut, hA))
    elif wA < wOut and hA >= hOut:
        SetImageROI(out, (0, 0, wA, hOut))
        SetImageROI(A, (0, 0, wA, hOut))
    else: # wA >= wOut and hA >= hOut:
        SetImageROI(A, (0, 0, wOut, hOut))
    cv.Copy(A, out)
    cv.ResetImageROI(out)
    cv.ResetImageROI(A)
    return out

def main():
    args = sys.argv[1:]
    imgsdir = args[0]
    
    imgpaths = []
    for dirpath, dirnames, filenames in os.walk(imgsdir):
        for imgname in [f for f in filenames if '.png' in f.lower()]:
            imgpaths.append(os.path.join(dirpath, imgname))
    
    t = time.time()
    print "Starting overlays..."
    minimg, maximg = make_minmax_overlay(imgpaths, do_align=True, rszFac=0.75)
    misc.imsave("_minimg_np.png", minimg)
    misc.imsave("_maximg_np.png", maximg)
    dur = time.time() - t
    print "...Finished overlays, {0} s".format(dur)

    t = time.time()
    print "Starting overlays..."
    minimg, maximg = overlay_minmax_cv(imgpaths, do_align=True, rszFac=0.75)
    dur = time.time() - t
    print "...Finished overlays, {0} s".format(dur)

    cv.SaveImage("_minimg.png", minimg)
    cv.SaveImage("_maximg.png", maximg)

    print "done."

main()
