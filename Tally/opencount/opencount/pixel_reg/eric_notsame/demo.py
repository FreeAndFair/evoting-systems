import sys
import scipy, scipy.misc

sys.path.append('..')
import shared

imgA = 'mail-04_party.png'
imgB = 'mail-78_party.png'

def main():
    patch = shared.standardImread(imgA, flatten=True)
    h, w = patch.shape
    bb = [0, h, 0, w]
    matches = shared.find_patch_matchesV1(patch, bb, (imgB,), threshold=0.0)
    filename,score1,score2,Ireg,y1,y2,x1,x2,rszFac = matches[0]

    print "Score1 is: {0}".format(score1)
    print "    This is low, which is good."
    print "Score2 is: {0}".format(score2)
    print "    This is super low, which is /bad/. The two patches are \
very different."

    print "I think this is the root of the problem: if I save the \
Ireg outputted by find_patch_matchesV1, then I get an all-black \
output image."
    print "Saving Ireg as: Ireg_out.png"
    scipy.misc.imsave('Ireg_out.png', Ireg)

if __name__ == '__main__':
    main()
