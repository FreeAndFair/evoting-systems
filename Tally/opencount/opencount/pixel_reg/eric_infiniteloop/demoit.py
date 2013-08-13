import sys
sys.path.append('..')
import shared

def main():
    patchpath = 'patch_tmp.png'
    regionpath = 'allpatches_tmp.png'
    imgpatch = shared.standardImread(patchpath, flatten=True)
    h, w = imgpatch.shape
    bb = [0, h-1, 0, w-1]
    matches = shared.find_patch_matchesV1(imgpatch, bb, (regionpath,))
    print 'Num Matches:', len(matches)

if __name__ == '__main__':
    main()


