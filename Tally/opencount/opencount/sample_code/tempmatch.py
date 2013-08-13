import time, pdb
import cv

"""
A short script that demonstrates how to use OpenCV's template matching.
To run the demo, just run the script:

    $ python tempmatch.py
"""

def bestmatch(A, B):
    """ Tries to find the image A within the (larger) image B.
    For instance, A could be a voting target, and B could be a
    contest.
    Input:
        cvMat A: Patch to search for
        cvMat B: Image to search over
    Output:
        (x,y) location on B of the best match for A.
    """
    # Tip: It's best to think of an image as an NxM matrix, where N 
    # is the number of rows (height) and M is the number of columns 
    # (width) This seems to be the convention in the image processing/CV 
    # community.
    w_A, h_A = A.cols, A.rows
    w_B, h_B = B.cols, B.rows
    
    # cv.MatchTemplate outputs a Response matrix (or 'Similarity'
    # matrix), which is a matrix containing values from [-1.0, 1.0].
    # If s_mat[i,j] is, say, 0.94, then s_mat is sort of claiming that:
    #     "With 0.94 confidence, I predict that A is present at image
    #     location (i,j)."
    # For the cv.CV_TM_CCOEFF_NORMED method, higher values is better -
    # thus, a response value of 1.0 means an exact match was found.
    s_mat = cv.CreateMat(h_B - h_A + 1, w_B - w_A + 1, cv.CV_32F)
    cv.MatchTemplate(B, A, s_mat, cv.CV_TM_CCOEFF_NORMED)
    
    # Now that we've run template matching, let's grab the location
    # of the highest response value from the similarity matrix s_mat.
    # We'll use the cv.MinMaxLoc function, which happens to give us the
    # locations+responses of the highest and lowest responses.
    minResp, maxResp, minLoc, maxLoc = cv.MinMaxLoc(s_mat)

    print "Highest response was {0}, found at {1}.".format(maxResp, maxLoc)
    print "Lowest response was {0}, found at {1}".format(minResp, minLoc)

    return maxLoc

def main():
    targetpath = 'target_oc.png'
    contestpath = 'contest_oc.png'

    # 1.) Load images via OpenCV. I use cv.LoadImageM instead of
    # cv.LoadImage, because I personally find it more convenient to
    # work with cvMat's (which cv.LoadImageM returns). cv.LoadImage,
    # on the other hand, returns IplImage instances.
    Itarget = cv.LoadImageM(targetpath, cv.CV_LOAD_IMAGE_GRAYSCALE)
    Icontest = cv.LoadImageM(contestpath, cv.CV_LOAD_IMAGE_GRAYSCALE)
    
    # 2.) Run template matching
    print "Running template matching..."
    t = time.time()
    (x, y) = bestmatch(Itarget, Icontest)
    dur = time.time() - t
    print "...Finished Running template matching ({0} s).".format(dur)

    # 3.) Mark on the image where template matching found the target,
    # and save it to the current directory.
    Icolor = cv.LoadImageM(contestpath, cv.CV_LOAD_IMAGE_COLOR)
    cv.Circle(Icolor, (x, y), 15, cv.RGB(0, 60, 255), thickness=4)
    cv.SaveImage("bestmatch_result.png", Icolor)
    print "Saved graphical output of template matching to: bestmatch_result.png."

    print "Done."

if __name__ == '__main__':
    main()

