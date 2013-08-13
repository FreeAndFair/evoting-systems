import os, sys, time, pdb
import cv
import numpy as np, scipy.misc

def find_matches(imgpaths, patch, C=0.8):
    """ Runs template matching to find PATCH in each IMGPATHS.
    Input:
        list imgpaths: [imgpath_i, ...]
        IplImage patch: 
        float C:
    Output:
        list matches, [[imgpath_i, (x,y), score_i], ...]
    """
    matches = {} # maps {str imgpath: [(x,y,score_i), ...]}
    for imgpath in imgpaths:
        img = cv.LoadImage(imgpath, cv.CV_LOAD_IMAGE_GRAYSCALE)
        img_smooth = cv.CreateImage((img.width, img.height), img.depth, img.channels)
        cv.Smooth(img, img_smooth, cv.CV_GAUSSIAN, param1=17,param2=17)
        M = cv.CreateMat(img.height-patch.height+1, img.width-patch.width+1, cv.CV_32F)
        cv.MatchTemplate(img_smooth, patch, M, cv.CV_TM_CCOEFF_NORMED)
        M_np = np.array(M)
        score = np.inf
        while score > C:
            M_idx = np.argmax(M_np)
            i = int(M_idx / M.cols)
            j = M_idx % M.cols
            score = M_np[i,j]
            if score < C:
                break
            matches.setdefault(imgpath, []).append((j, i, score))
            # Suppression
            M_np[i-(patch.height/3):i+(patch.height/3),
                 j-(patch.width/3):j+(patch.width/3)] = -1.0
    return matches

def main():
    args = sys.argv[1:]
    imgpaths = ['contest_oc.png']
    T = cv.LoadImage('target_oc.png', cv.CV_LOAD_IMAGE_GRAYSCALE)
    T_smooth = cv.CreateImage((T.width,T.height),T.depth,T.channels)
    cv.Smooth(T, T_smooth, cv.CV_GAUSSIAN, param1=17, param2=17)
    allmatches = find_matches(imgpaths, T_smooth, C=0.8)
    for imgpath, matches in allmatches.iteritems():
        print "For image: {0}, {1} matches found.".format(imgpath, len(matches))
        I = cv.LoadImage(imgpath, cv.CV_LOAD_IMAGE_COLOR)
        for (x, y, score) in matches:
            cv.Circle(I, (x,y), 15, cv.RGB(0, 60, 255), thickness=4)
        cv.SaveImage("allmatches_result.png", I)
    print "Done."

if __name__ == '__main__':
    main()
