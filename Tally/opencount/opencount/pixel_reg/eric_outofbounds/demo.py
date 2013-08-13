import sys
sys.path.append('../')

import shared

img1path = '_err_img1.png'

def main():
    regions = ['extracted_digitpatches/precinct/0_exemplar.png',
               'extracted_digitpatches/precinct/1_exemplar.png', 
               'extracted_digitpatches/precinct/2_exemplar.png']
    img1 = shared.standardImread(img1path, flatten=True)
    (h,w) = img1.shape
    bb = [0, h-1, 0, w-1]
    print "bb is:", bb
    matches = shared.find_patch_matchesV1(img1, bb, regions, threshold=0.7)
    print 'Found {0} number of matches.'.format(len(matches))

if __name__ == '__main__':
    main()

