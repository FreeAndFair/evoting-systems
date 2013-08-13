import multiprocessing, time
from PIL import Image, ImageChops, ImageOps
from time import clock
import numpy as np
import scipy.misc as misc
import cv
import sys
import random

sys.path.append('..')
import grouping.partask as partask
from pixel_reg.imagesAlign import imagesAlign

def minmax_cv_par(imgpaths, do_align=False, rszFac=1.0, trfm_type='rigid',
                  minArea=np.power(2, 16), bbs_map=None, numProcs=None,
                  imgCache=None):
    """ A parallel-wrapper for minmax_cv_v2. 
    Note: For some reason, this is ~10X slower than just calling minmax_cv
    and doing it in a single process. Not sure why...
    NOTE: Currently deprecated. We switched back to using a numpy-based
          overlay-generation function, for ease (make_overlay_minmax)
    """
    if numProcs == None:
        numProcs = multiprocessing.cpu_count()
    if numProcs == 1:
        return minmax_cv(imgpaths, do_align=do_align, rszFac=rszFac, trfm_type=type,
                         minArea=minArea, bbs_map=bbs_map, imgCache=imgCache)
    imgpaths = imgpaths[:]
    Iref_imP = imgpaths.pop()
    Imin_str, Imax_str, size = partask.do_partask(_minmax_cv_v2_wrapper, 
                                                  imgpaths,
                                                  _args=(Iref_imP, do_align, rszFac, type, minArea, bbs_map),
                                                  init=(None, None, None),
                                                  combfn=_minmax_combfn,
                                                  N=numProcs)
    return str2iplimage(Imin_str, size), str2iplimage(Imax_str, size)

def _minmax_combfn(a, b):
    # Unfortunately, things passed to multiprocessing must be pickle'able,
    # but IplImages are /not/ pickle'able. So, I must turn the IplImage into
    # its string (via .tostring()), then re-morph it back into IplImage. 
    IminA_str, ImaxA_str, size = a
    IminB_str, ImaxB_str, size = b
    IminB = str2iplimage(IminB_str, size)
    ImaxB = str2iplimage(ImaxB_str, size)
    if IminA_str == None:
        return IminB.tostring(), ImaxB.tostring(), size
    IminA = str2iplimage(IminA_str, size)
    ImaxA = str2iplimage(ImaxA_str, size)
    cv.Min(IminA, IminB, IminB)
    cv.Max(ImaxA, ImaxB, ImaxB)
    return IminB.tostring(), ImaxB.tostring(), size

def str2iplimage(A_str, size):
    A = cv.CreateImageHeader(size, cv.IPL_DEPTH_8U, 1)
    cv.SetData(A, A_str)
    return A

def _minmax_cv_v2_wrapper(imgpaths, *args, **kwargs):
    return minmax_cv_v2(imgpaths, *args, **kwargs)
def minmax_cv_v2(imgpaths, Iref_imP=None, do_align=False, rszFac=1.0, trfm_type='rigid',
                 minArea=np.power(2, 16), bbs_map=None):
    """ Computes the overlays of IMGPATHS, but uses the IREF_IMP as the
    reference image to align against, if DO_ALIGN is True. Mainly a 
    function written for the parallel version (minmax_cv is still fine for
    single-process use).
    """
    bbs_map = {} if bbs_map == None else bbs_map
    if do_align:
        Iref = cv.LoadImage(Iref_imP, cv.CV_LOAD_IMAGE_GRAYSCALE)
        bbRef = bbs_map.get(Iref_imP, None)
        if bbRef:
            coords = tuple(map(int, (bbRef[0], bbRef[1], bbRef[2]-bbRef[0], bbRef[3]-bbRef[1])))
            cv.SetImageROI(Iref)
    else:
        Iref = None
    # 0.) Prep first image
    imgpath0 = imgpaths[0]
    Imin = cv.LoadImage(imgpath0, cv.CV_LOAD_IMAGE_GRAYSCALE)
    bb0 = bbs_map.get(imgpath0, None)
    if bb0:
        coords = tuple(map(int, (bb0[0], bb0[1], bb0[2]-bb0[0], bb0[3]-bb0[1])))
        cv.SetImageROI(Imin)
    Imax = cv.CloneImage(Imin)
    Iref_np = (iplimage2np(cv.CloneImage(Iref)) / 255.0) if do_align else None
    for imgpath in imgpaths[1:]:
        I = cv.LoadImage(imgpath, cv.CV_LOAD_IMAGE_GRAYSCALE)
        bb = bbs_map.get(imgpath, None)
        if bb:
            bb = tuple(map(int, bb))
            cv.SetImageROI(I, (bb[0], bb[1], bb[2]-bb[0], bb[3]-bb[1]))
        Iout = matchsize(I, Imax)
        if do_align:
            tmp_np = iplimage2np(cv.CloneImage(Iout)) / 255.0
            H, Ireg, err = imagesAlign(tmp_np, Iref, trfm_type=type, fillval=0, rszFac=rszFac, minArea=minArea)
            Ireg *= 255.0
            Ireg = Ireg.astype('uint8')
            Iout = np2iplimage(Ireg)
        cv.Max(Iout, Imax, Imax)
        cv.Min(Iout, Imin, Imin)
    return Imin.tostring(), Imax.tostring(), cv.GetSize(Imin)
            
def minmax_cv(imgpaths, do_align=False, rszFac=1.0, trfm_type='rigid',
              minArea=np.power(2, 16), bbs_map=None, imgCache=None):
    """ Generates min/max overlays for IMGPATHS. If DO_ALIGN is
    True, then this also aligns every image to the first image in
    IMGPATHS.
    Input:
        list IMGPATHS: [str imgpath_i, ...]
        bool DO_ALIGN:
        float RSZFAC: Resizing factor for alignment.
        dict BBS_MAP: maps {str imgpath: (x1,y1,x2,y2)}
    Output:
        cvMat minimg, cvMat maximg.
    """
    def load_image(imgpath):
        if imgCache == None:
            return cv.LoadImage(imgpath, cv.CV_LOAD_IMAGE_GRAYSCALE)
        else:
            ((img, imgpath), isHit) = imgCache.load(imgpath)
            return img

    if bbs_map == None:
        bbs_map = {}
    imgpath = imgpaths[0]
    bb0 = bbs_map.get(imgpath, None)
    Imin = load_image(imgpath)
    if bb0:
        coords = (bb0[0], bb0[1], bb0[2]-bb0[0], bb0[3]-bb0[1])
        coords = tuple(map(int, coords))
        cv.SetImageROI(Imin, coords)
    Imax = cv.CloneImage(Imin)
    
    #Iref = np.asarray(cv.CloneImage(Imin)) if do_align else None
    Iref = (iplimage2np(cv.CloneImage(Imin)) / 255.0) if do_align else None
    for imgpath in imgpaths[1:]:
        I = load_image(imgpath)
        bb = bbs_map.get(imgpath, None)
        if bb:
            bb = tuple(map(int, bb))
            cv.SetImageROI(I, (bb[0], bb[1], bb[2]-bb[0], bb[3]-bb[1]))
        Iout = matchsize(I, Imax)
        if do_align:
            tmp_np = iplimage2np(cv.CloneImage(Iout)) / 255.0
            H, Ireg, err = imagesAlign(tmp_np, Iref, trfm_type=trfm_type, fillval=0, rszFac=rszFac, minArea=minArea)
            Ireg *= 255.0
            Ireg = Ireg.astype('uint8')
            Iout = np2iplimage(Ireg)
        cv.Max(Iout, Imax, Imax)
        cv.Min(Iout, Imin, Imin)
    return Imin, Imax

def minmax_cv_V2(imgs, do_align=False, rszFac=1.0, trfm_type='rigid',
                 minArea=np.power(2, 16)):
    """ Just like minmax_cv(), but accepts a list of cvMat's instead
    of a list of imgpaths. If you're planning on generating overlays
    of tens-of-thousands of images, calling this function might result
    in a gross-amount of memory usage (since this function keeps them
    all in memory at once).
    """
    Imin = cv.CloneImage(imgs[0])
    Imax = cv.CloneImage(Imin)
    #Iref = np.asarray(cv.CloneImage(Imin)) if do_align else None
    Iref = (iplimage2np(cv.CloneImage(Imin)) / 255.0) if do_align else None
    for I in imgs[1:]:
        Iout = matchsize(I, Imax)
        if do_align:
            tmp_np = iplimage2np(cv.CloneImage(Iout)) / 255.0
            H, Ireg, err = imagesAlign(tmp_np, Iref, trfm_type=trfm_type, fillval=0, rszFac=rszFac, minArea=minArea)
            Ireg *= 255.0
            Ireg = Ireg.astype('uint8')
            Iout = np2iplimage(Ireg)

        cv.Max(Iout, Imax, Imax)
        cv.Min(Iout, Imin, Imin)
    return Imin, Imax

def matchsize(A, B):
    """ Given two cvMats A, B, returns a cropped/padded version of
    A that has the same dimensions as B.
    """
    wA, hA = cv.GetSize(A)
    wB, hB = cv.GetSize(B)
    if wA == wB and hA == hB:
        return A
    SetImageROI = cv.SetImageROI
    out = cv.CreateImage((wB, hB), A.depth, A.channels)
    wOut, hOut = cv.GetSize(out)
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
def iplimage2np(img):
    #a = np.frombuffer(img.tostring(), dtype=np.uint8)
    #a.shape = img.height, img.width
    a = np.fromstring(img.tostring(), dtype=np.uint8)
    w, h = cv.GetSize(img)
    a = a.reshape(h,w)
    return a

def np2iplimage(array):
    img = cv.CreateImageHeader((array.shape[1], array.shape[0]), cv.IPL_DEPTH_8U, 1)
    cv.SetData(img, array.tostring(), array.dtype.itemsize * 1 * array.shape[1])
    return img

def make_minmax_overlay(imgpaths, do_align=False, rszFac=1.0, imgCache=None,
                        queue_mygauge=None,
                        bindataP=None):
    """ Generates the min/max overlays of a set of imagepaths.
    If the images in IMGPATHS are of different size, then this function
    arbitrarily chooses the first image to be the size of the output
    IMIN, IMAX.
    Input:
        list IMGPATHS:
        bool DO_ALIGN:
            If True, then this will choose an arbitrary image A as a reference
            image, and align every image in IMGPATHS to A.
        float RSZFAC:
            Which scale to perform image alignment at.
        obj IMGCACHE:
            If given, the function will use IMGCACHE, an instance of the
            ImageCache class, to load images. Otherwise, it will always
            read each image from disk.
    Output:
        (nparray Imin, nparray Imax).
    """
    # TODO: Implement with bbs_map
    def load_image(imgpath):
        if imgCache == None:
            return misc.imread(imgpath, flatten=True)
        elif bindataP != None:
            (img, tag), isHit = imgCache.load_binarydat(imgpath, bindataP)
            return img
        else:
            (img, imgpath), isHit = imgCache.load(imgpath)
            return img
    overlayMin, overlayMax = None, None
    Iref = None
    for path in imgpaths:
        img = load_image(path)
        if do_align and Iref == None:
            Iref = img
        elif do_align:
            (H, img, err) = imagesAlign(img, Iref, fillval=0, rszFac=rszFac)
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
        if queue_mygauge != None:
            queue_mygauge.put(True)

    # HACK: To prevent auto-dynamic-rescaling bugs, where an all-white
    # image is interpreted as all-black, artificially insert a 0.0 at (0,0).
    # See: http://stefaanlippens.net/scipy_unscaledimsave
    overlayMin[0,0] = 0.0
    overlayMax[0,0] = 0.0

    return overlayMin, overlayMax

def make_minmax_overlay2(imgs, do_align=False, rszFac=1.0):
    overlayMin, overlayMax = None, None
    Iref = None
    for img in imgs:
        if do_align and Iref == None:
            Iref = img
        elif do_align:
            (H, img, err) = imagesAlign(img, Iref, fillval=0, rszFac=rszFac)
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
    out = np.zeros(shape, dtype=img.dtype)
    i = min(img.shape[0], out.shape[0])
    j = min(img.shape[1], out.shape[1])
    out[0:i,0:j] = img[0:i, 0:j]
    return out

"""
Originally written by Arel Cordero. Modified by Eric Kim (3/27/2011)
in order to make overlay_im more efficient (if you want to overlay
thousands of PIL images, PIL will crash if too many Image objects
are open at once.
"""

# Colors for overlay
WHITE  = (255,255,255)
COLOR1 = (255,0,0)
COLOR2 = (0,0,255)

# Colors represented as arrays
WHITE_ARRAY  = np.array(WHITE)
COLOR1_ARRAY = np.array(COLOR1)
COLOR2_ARRAY = np.array(COLOR2)

def overlay_im_orig(images):
    if not images:
        return None
    min_im = None
    max_im = None
    for im in images:
        min_im = im if min_im == None else ImageChops.darker(im, min_im)
        max_im = im if max_im == None else ImageChops.lighter(im, max_im)
    overlay   = Image.new("RGBA", images[0].size, (255,255,255,255))
    overlay.paste(Image.new("RGB", images[0].size, COLOR1), None, ImageOps.invert(min_im))
    overlay.paste(Image.new("RGB", images[0].size, COLOR2), None, ImageOps.invert(max_im))
    return overlay

"""
Modified - 3/27/2011: Now takes in a list of image paths (as strings).
In the past, 'images' referred to a list of PIL Image instances - this
would crash however if there were thousands of PIL Image instances open
at once.         - Eric Kim
"""
def overlay_im(images, include_min_max=False):
    """
    Input:
        images: a list of image paths.
        include_min_max: A boolean (True/False) as to whether or not the
            user would like to also save the min and max images.
    Output:
        The overlay image.
    """
    if not images:
        return None
        
    # determine min- and max-images
    min_im = None
    max_im = None
    for im in images:
        pil_img = Image.open(im).convert('L')
        min_im = pil_img if min_im == None else ImageChops.darker(pil_img, min_im)
        max_im = pil_img if max_im == None else ImageChops.lighter(pil_img, max_im)

    # represent images as matrices
    min_im_mat    = np.asarray(min_im)
    max_im_mat    = np.asarray(max_im)

    # calculate alpha and beta
    epsilon = 0.01
    alpha   = min_im_mat / 255.0
    beta    = (max_im_mat - min_im_mat) / ((255.0 - min_im_mat) + epsilon)  # To avoid div by 0
    
    # create overlay image matrix
    hue_mat     = beta[:,:,np.newaxis] * COLOR1_ARRAY[np.newaxis,np.newaxis,:]  +  (1.0 - beta[:,:,np.newaxis]) * COLOR2_ARRAY[np.newaxis,np.newaxis,:]
    overlay_mat = alpha[:,:,np.newaxis] * WHITE_ARRAY[np.newaxis,np.newaxis,:]  +  (1.0 - alpha[:,:,np.newaxis]) * hue_mat
    
    # convert back to image
    # (using workaround for PIL not correctly creating RGB images from arrays)
    overlay_mat = overlay_mat.astype("uint8") # convert to appropriate type for images
    r = Image.fromarray(overlay_mat[:,:,0])
    g = Image.fromarray(overlay_mat[:,:,1])
    b = Image.fromarray(overlay_mat[:,:,2])
    overlay = Image.merge("RGB", (r,g,b))

    if include_min_max:
        return (overlay, min_im, max_im)
    else:
        return overlay

def normal_box(box, size):
    nb = np.asarray(box).copy()
    if box[2]<box[0]:
        nb[0] = box[2]
        nb[2] = box[0]
    if box[3]<box[1]:
        nb[1] = box[3]
        nb[3] = box[1]
    nb = [max(nb[0],0), max(nb[1],0), min(nb[2],size[0]-1), min(nb[3],size[1]-1)]
    return nb

def partition_im(images, box):
    if not images:
        return None
    box = normal_box(box, images[0].size)
    N = len(images)
    M = (1+(box[2]-box[0])) * (1+(box[3]-box[1]))
    stack = np.empty((N, M), 'float64')
    for i,im in enumerate(images):
        row = np.array(im,'float64')[box[1]:box[3]+1, box[0]:box[2]+1].ravel()
        stack[i] = row
    partition = [[],[]]
    ave_intensity = stack.mean(1) - stack.mean()
    means         = kmeans(ave_intensity, 2)
    thresh        = sum(means) / 2
    for i in range(len(images)):
        if ave_intensity[i] < thresh:
            partition[0].append(i)
        else:
            partition[1].append(i)
    if len(partition[0]) > len(partition[1]):
        partition.reverse()
    #print ["%3.5f"%f for f in means]
    #print ["%3.5f"%f for f in ave_intensity]
    #print ["%3.5f"%f for f in stack.min(1)]
    #print thresh
    return partition # ave_intensity, [len(partition[0]), len(partition[1])] 

def ave(l):
    return sum(l) / float(len(l))

def var(l, a=None):
    a = ave(l) if a==None else a
    return sum( [(i-a)**2 for i in l] ) / float(len(l))

def histogram_mean(l, offset=0):
    return offset + sum([l[i]*i for i in range(len(l))]) / float(sum(l))
    
# See: http://en.wikipedia.org/wiki/Otsu's_method
def otsu(gray_im):
    """
Computes the optimal global threshold for a gray-scale image by maximizing the
variance *between* the two classes of pixels (i.e., light and dark). Operates
efficiently by using the image histogram of the input image.

i.e., use:

threshold = otsu( im )
"""
    hist = gray_im.histogram()
    best = None
    for t in range(len(hist)):
        left  = hist[:(t+1)] 
        right = hist[(t+1):]
        if sum(left) * sum(right) == 0: continue # skip degenerate cases
        inter_class_variance = sum(left) * sum(right) * (histogram_mean(left) - histogram_mean(right, len(left)))**2
        # print "%s, %5.5f" % (t, inter_class_variance)
        if best == None or inter_class_variance > best[1]:
            best = (t, inter_class_variance)
    return best[0]

def kmeans(itemlist, k=2, rounds=10, iterations=5):
    overall_best = None
    for n in range(iterations):
        means  = random.sample(list(itemlist),k) # Want any k distinct items.
        for i in range(rounds):
            # print "round", i
            counts   = [0.0] * k
            newmeans = [0.0] * k
            score    = 0
            for l in itemlist:
                best = None
                for n in range(k):
                    if not best or abs(l-means[n]) < best[0]:
                        best = (abs(l-means[n]), n, l)
                counts[best[1]]   += 1
                score += best[0]**2
                newmeans[best[1]] = newmeans[best[1]] - (newmeans[best[1]] - best[2]) * (1/(counts[best[1]]))
            means = newmeans
            # print score, means
        if not overall_best or score < overall_best[0]:
            if overall_best: print "K-means: Yay! Iteration did something."
            overall_best = (score, means)
    return overall_best[1]

def autothreshold(gray_im, method="otsu"):
    """method can be either "otsu" or "kmeans"."""
    if   method == "otsu":
        t = otsu(gray_im)
    elif method == "kmeans":
        t = ave(kmeans(list(gray_im.getdata())))
    return gray_im.point(lambda x: 0 if x < t else 255)  # < or <= ?

def abs_sum(gray_im, windowsize, searchvalue=None):
    """A linear time operation to calculate the absolute sum of pixels within a sub-region of arbitrary size at each point in the image.
    This can be used to pre-process an image to reduce the search time for template matching.
    
    NOTE: if a search value is passed in, then the sum is the number of pixels with that intensity value. Otherwise, it's the absolute sum.
    
    NOTE: the absolute sum of the subregion is stored in the returned (flattened) list by it's LOWER RIGHT index.
    
    See, "Fast Image Template and Dictionary Matching Algorithms," Sung-Hyuk Cha, 1997.
    """
    colsum = [0] * gray_im.size[0] * gray_im.size[1]
    totsum = [0] * gray_im.size[0] * gray_im.size[1]
    c1 = clock()
    if searchvalue != None:
        data   = list(gray_im.point(lambda x: 1 if x==searchvalue else 0).getdata()) # init as 0/1 thresholded image data (vs 0/255)
    else:
        data   = list(gray_im.getdata())
    pos = 0
    for j in range(gray_im.size[1]):
        for i in range(gray_im.size[0]):
            colsum[pos] = data[pos]
            if j-1                 >= 0: colsum[pos] += colsum[pos-gray_im.size[0]] # add the subtotal from point above
            if j-windowsize[1]     >= 0: colsum[pos] -= data[pos-(gray_im.size[0]*windowsize[1])] # keep within vertical window

            totsum[pos] = colsum[pos]
            if i-1                 >= 0: totsum[pos] += totsum[pos-1] # add point total to the left
            if i-windowsize[0]     >= 0: totsum[pos] -= colsum[pos-windowsize[0]] # keep within horizontal window

            pos += 1
    sys.stderr.write("local sum: %3.3fs\n" % (clock()-c1))
    return totsum

def local_hist(gray_im, windowsize, buckets=4):
    """
    See, "Fast Image Template and Dictionary Matching Algorithms," Sung-Hyuk Cha, 1997.
    """
    colhist = [0] * gray_im.size[0] * gray_im.size[1] * buckets
    tothist = [0] * gray_im.size[0] * gray_im.size[1] * buckets
    denominator = (256.0/buckets)
    c1 = clock()
    data   = list(gray_im.getdata())
    pos      = 0
    data_pos = 0
    for j in range(gray_im.size[1]):
        for i in range(gray_im.size[0]):
            bucket       = int(data[data_pos] / denominator)
            colhist[pos + bucket] += 1
            if j-1                 >= 0:
                # add the column histogram of the point above
                for k in range(buckets):
                    colhist[pos + k] += colhist[(pos - (gray_im.size[0]*buckets)) + k]
            if j-windowsize[1]     >= 0:
                # keep within vertical window
                bucket_above = int( data[data_pos-(gray_im.size[0]*windowsize[1])] / denominator)
                colhist[pos + bucket_above] -= 1

            for k in range(buckets):
                tothist[pos+k] = colhist[pos+k] # add histogram of this column
                if i-1                 >= 0: tothist[pos+k] += tothist[(pos-buckets)+k] # add histogram of the window to the left
                if i-windowsize[0]     >= 0: tothist[pos+k] -= colhist[(pos-(buckets*windowsize[0]))+k] # keep within horizontal window

            pos      += buckets
            data_pos += 1
    sys.stderr.write("local histogram: %3.3fs\n" % (clock()-c1))
    return tothist

def h_dist(hist1, hist2, buckets=4):
    diff  = 0
    hsum1 = float(sum(hist1) + buckets)
    hsum2 = float(sum(hist2) + buckets)
    for i in range(buckets):
        diff += abs((hist1[i]+1)/hsum1 - (hist2[i]+1)/hsum2)
    return diff
    

"""
Euclidean distance transform
See: http://www.logarithmic.net/pfh/blog/01185880752
"""

import numpy

def _upscan(f):
    for i, fi in enumerate(f):
        if fi == numpy.inf: continue
        for j in xrange(1,i+1):
            x = fi+j*j
            if f[i-j] < x: break
            f[i-j] = x

def distance_transform(bitmap):
    f = numpy.where(bitmap, 0.0, numpy.inf)
    for i in xrange(f.shape[0]):
        _upscan(f[i,:])
        _upscan(f[i,::-1])
    for i in xrange(f.shape[1]):
        _upscan(f[:,i])
        _upscan(f[::-1,i])
    numpy.sqrt(f,f)
    return f

"""
if __name__ == '__main__':
    try:
        import psyco
        psyco.full()
    except ImportError:
        pass
    
    import pylab
    from numpy import random
    vec = random.random((1000,1000)) < 0.0001
    vec[100:400,500:900] = 1
    vec[500:900,500:900] = 0

    pylab.imshow(distance_transform(vec))
    pylab.show()
"""

