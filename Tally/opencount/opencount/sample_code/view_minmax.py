import os, sys, time, pdb
import cv

sys.path.append('..')
import grouping.make_overlays as make_overlays

"""
A quick script that demos how to create Min/Max overlays.

Usage:
    python view_minmax.py IMGSDIR

where IMGSDIR is a directory containing the images you'd like to
overlay, i.e.:

    python view_minmax.py 005/
"""

def main():
    args = sys.argv[1:]
    imgsdir = args[0]

    imgpaths = []
    for dirpath, dirnames, filenames in os.walk(imgsdir):
        for imgname in [f for f in filenames if isimgext(f)]:
            imgpath = os.path.join(dirpath, imgname)
            imgpaths.append(imgpath)
    
    print "Computing min/max overlays..."
    t = time.time()
    Imin, Imax = make_overlays.minmax_cv(imgpaths, do_align=True, rszFac=0.75)
    dur = time.time() - t
    print "...Finished Computing min/max overlays ({0} s).".format(dur)
    print "...Saving as: Imin.png, Imax.png..."
    cv.SaveImage("Imin.png", Imin)
    cv.SaveImage("Imax.png", Imax)

    print "...Or, if you happen to instead have a list of images, \
instead of a list of image paths:"
    imgs = [cv.LoadImage(imgpath, cv.CV_LOAD_IMAGE_GRAYSCALE) for imgpath in imgpaths]
    t = time.time()
    Imin_2, Imax_2 = make_overlays.minmax_cv_V2(imgs, do_align=True, rszFac=0.75)
    dur = time.time() - t
    print "...Finished Computing min/max overlays V2 ({0} s).".format(dur)
    print "...Saving as: IminV2.png, ImaxV2.png..."
    cv.SaveImage("IminV2.png", Imin_2)
    cv.SaveImage("ImaxV2.png", Imax_2)

    print "Done."

def isimgext(f):
    return os.path.splitext(f)[1].lower() in ('.png', 'jpeg', '.jpg',
                                              '.bmp', '.tif')

if __name__ == "__main__":
    main()

