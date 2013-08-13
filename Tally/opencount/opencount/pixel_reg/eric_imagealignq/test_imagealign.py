import sys
import numpy as np, scipy.misc
sys.path.append('..')

import shared
import imagesAlign

"""
Usage:
    python test_imagesalign.py imgA.png imgB.png
"""

def main():
    args = sys.argv[1:]
    if not args:
        imgA = 'imgA.png'
        imgB = 'imgB.png'
    else:
        imgA = args[0]
        imgB = args[1]

    Ia = shared.standardImread(imgA, True)
    Ib = shared.standardImread(imgB, True)

    print "Aligning {0} to {1}...".format(imgA, imgB)
    H, Ireg, err = imagesAlign.imagesAlign(Ia, Ib)
    Ireg_nonan = np.nan_to_num(Ireg)

    scipy.misc.imsave("_IregA.png", Ireg_nonan)

    print "Done, outputted result to: _IregA.png"


main()
