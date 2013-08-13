import sys
sys.path.append('..')
import cv
import numpy as np

import shared

"""
A short script that reveals a bug when converting np images to 
openCV images, when the np array is a float from [0.0, 1.0].

cv_imgBAD is created from a np array with floats between [0.0, 1.0].
    The image is all black.

cv_imgGOOD is created from the same np array, but scaled by 255.0, so
    that the values range from [0.0, 255.0].
    The image is 'correct'.
"""

Ipath = 'party.png'

def main():
    I_np = shared.standardImread(Ipath, flatten=True)
    I_np = shared.prepOpenCV(I_np)

    cv_imgBAD = cv.fromarray(np.copy(I_np))
    cv.SaveImage("party_CV_BAD.png", cv_imgBAD)

    cv_imgGOOD = cv.fromarray(np.copy(I_np) * 255.0)
    cv.SaveImage("party_CV_GOOD.png", cv_imgGOOD)

    print "Done."

if __name__ == '__main__':
    main()

