import os, sys, pdb, traceback
import cv, numpy as np, scipy.misc

"""
A quick-and-dirty demo script that, given three cooresponding points
on two different images A, B, aligns B to A by finding the affine
transformation matrix M that fits B to A, and then applying M to B.

Usage:
    python find_transform.py
    
A nice explanation behind the theory is found at:
    http://docs.opencv.org/doc/tutorials/imgproc/imgtrans/warp_affine/warp_affine.html
"""

def align_affine(imgA, imgB, ptsA, ptsB):
    """ Aligns IMGB to IMGA, given that the points in PTSA correspond
    to the points in PTSB. Returns both the aligned IMGB and the
    affine transformation matrix.    
    """
    # 1.) Assume that transformation is 'rigid' (translation, rotation,
    # scaling). Solve the equation:
    #   Mx = x'
    # where x is the coordinates in imgB: (x, y, 1)
    # x' is the coordinates in imgA: (x', y', 1)
    # and M is the affine transformation matrix, which is a 2x3
    # matrix consisting of the affine-trans. coefficients:
    #     M  =  | A B |  =  | a_00 a_01 b_0 |
    #                       | a_10 a_11 b_1 |
    # where A is the rotation+scaling matrix, B is the translation
    # matrix, and | A B | is the augmented matrix (that allows us to
    # apply an affine trans. to a point (x, y) with a single matrix
    # operation:    
    #     (x',y',1) = M * (x,y,1)
    
    mapMat = cv.CreateMat(2, 3, cv.CV_32F)
    # Note: Here, we use the three pairs of cooresponding points to
    # solve for the affine transformation matrix M.
    cv.GetAffineTransform(ptsB, ptsA, mapMat)
    
    # 2.) Now that we have the affine transformation matrix M, we
    # apply it to imgB to align it to imgA:
    outMat = cv.CreateMat(imgB.rows, imgB.cols, imgB.type)
    cv.WarpAffine(imgB, outMat, mapMat)
    
    return outMat, mapMat

def main():
    imgNormalP = 'contest_oc.png'
    imgRotatedP = 'contest_oc_rot.png'
    
    imgA = cv.LoadImageM(imgNormalP, cv.CV_LOAD_IMAGE_GRAYSCALE)
    imgB = cv.LoadImageM(imgRotatedP, cv.CV_LOAD_IMAGE_GRAYSCALE)
    
    # A is Normal, B is Rotated
    # 0.) Get corners (upperleft,upperright,lowerleft,lowerright)
    # pA_0 corresponds to pB_0, etc...
    pA_0 = (28, 29)             # UpperLeft
    pA_1 = (509, 30)            # UpperRight    
    pA_2 = (29, 531)            # LowerLeft    
    pA_3 = (509, 530)           # LowerRight
    
    pB_0 = (109, 77)            # UpperLeft
    pB_1 = (587, 110)           # UpperRight
    pB_2 = (76, 578)            # LowerLeft
    pB_3 = (556, 606)           # LowerRight

    imgB_align, M = align_affine(imgA, imgB, (pA_0, pA_1, pA_2),
                                (pB_0, pB_1, pB_2))

    cv.SaveImage("_imgB_align.png", imgB_align)
    
    print "Done -- saved aligned image to: _imgB_align.png."
    print
    print "AffineMat found:"
    print np.array(M)
    
    print
    
    print "Note: You'll notice that _imgB_align.png still isn't \
'perfect' (it's still a tiny bit skewed), despite the fact that imgB \
was created by rotating imgA! This is likely due to imperfections in \
the point coorespondences, as I simply eye-balled the pixel coords."
    
if __name__ == '__main__':
    main()
