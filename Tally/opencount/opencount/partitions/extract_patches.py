import os, sys, multiprocessing, thread
import cv
sys.path.append('..')
import grouping.partask as partask

def extract(imgpatches, do_threshold=None, manager=None, queue_mygauge=None):
    """
    Input:
        dict IMGPATCHES: {imgpath: [((x1,y1,x2,y2), isflip, outpath, tag), ...]}
        obj MANAGER:
            Pass if you want to do MyGauge-related updates (to be used
            with an associated Queue instance, QUEUE_MYGAUGE.
        obj QUEUE_MYGAUGE:
            The Queue instance (owned by MANAGER) which is used to 
            communicate cross-process to a MyGauge instance.
    Output:
        dict IMG2PATCH: {(imgpath, tag): patchpath},
        dict PATCH2STUFF. {patchpath: (imgpath, (x1,y1,x2,y2), tag)}.
    """
    return partask.do_partask(_extract_patches, imgpatches,
                              _args=(do_threshold, queue_mygauge),
                              manager=manager,
                              combfn=_combfn,
                              init=({}, {}),
                              N=None)

def _extract_patches(imgpatches, (do_threshold, queue_mygauge)):
    img2patch = {}
    patch2stuff = {}
    for imgpath, tups in imgpatches.iteritems():
        I = cv.LoadImage(imgpath, cv.CV_LOAD_IMAGE_UNCHANGED)
        if tups and tups[0][1]:
            # Image should be flipped
            cv.Flip(I, I, flipMode=-1)
        if do_threshold != None:
            cv.Threshold(I, I, do_threshold, 255.0, cv.CV_THRESH_BINARY)
        for ((x1,y1,x2,y2), isflip, outpath, tag) in tups:
            try: os.makedirs(os.path.split(outpath)[0])
            except: pass
            cv.SetImageROI(I, tuple(map(int, (x1,y1,x2-x1,y2-y1))))
            cv.SaveImage(outpath, I)
            img2patch[(imgpath, tag)] = outpath
            patch2stuff[outpath] = (imgpath, (x1,y1,x2,y2), tag)
        if queue_mygauge != None:
            # Updates the MyGauge widget
            queue_mygauge.put(True)
    return img2patch, patch2stuff

def _combfn(a, b):
    img2patchA, patch2stuffA = a
    img2patchB, patch2stuffB = b
    return (dict(img2patchA.items() + img2patchB.items()),
            dict(patch2stuffA.items() + patch2stuffB.items()))
