import multiprocessing as mp
import traceback, pdb, time, os
import numpy as np
import cv
import csv
import string
import math
import imagesAlign as lk
from scipy import misc
from wx.lib.pubsub import Publisher

MAX_PRECINCT_PATCH_DIM=800
MIN_PRECINCT_PATCH_DIM=20
MAX_PRECINCT_PATCH_DISPLAY=800
FLIP_CHECK_HEIGHT=200
COARSE_BALLOT_REG_HEIGHT=725#500
LOCAL_PATCH_REG_HEIGHT=250
MAX_DIFF_HEIGHT=10

# The minimum required dimension of any image dimension.
MIN_IMG_DIM = 4

def imtransform(I,H0,fillval=np.nan):
    # transform image using center as origin
    if len(I.shape)==3:
        Iout=np.copy(I)
        Iout[:,:,0]=imtransform(I[:,:,0],H0,fillval=fillval)
        Iout[:,:,1]=imtransform(I[:,:,1],H0,fillval=fillval)
        Iout[:,:,2]=imtransform(I[:,:,2],H0,fillval=fillval)
        return Iout
    else:
        T0=np.eye(3); T0[0,2]=I.shape[1]/2.0; T0[1,2]=I.shape[0]/2.0
        T1=np.eye(3); T1[0,2]=-I.shape[1]/2.0; T1[1,2]=-I.shape[0]/2.0
        H=np.dot(np.dot(T0,H0),T1)

        # transform each channel separately
        if not I.flags.c_contiguous:
            I = np.copy(I)

        Icv=cv.fromarray(I)
        I1cv=cv.CreateMat(I.shape[0],I.shape[1],Icv.type)

        H = H[:2]
        H = cv.fromarray(H)
        #cv.WarpPerspective(Icv,I1cv,cv.fromarray(np.copy(H)),fillval=-1);
        cv.WarpAffine(Icv,I1cv,H)#,fillval=fillval);
        I1 = np.asarray(I1cv)
        #I1[np.nonzero(I1<0)]=fillval
        return I1

def imtransform2(I,H0,fillval=3.0):
    # transform image using center as origin
    if len(I.shape)==3:
        Iout=np.copy(I)
        Iout[:,:,0]=imtransform2(I[:,:,0],H0,fillval=fillval)
        Iout[:,:,1]=imtransform2(I[:,:,1],H0,fillval=fillval)
        Iout[:,:,2]=imtransform2(I[:,:,2],H0,fillval=fillval)
        return Iout
    else:
        T0=np.eye(3); T0[0,2]=I.shape[1]/2.0; T0[1,2]=I.shape[0]/2.0
        T1=np.eye(3); T1[0,2]=-I.shape[1]/2.0; T1[1,2]=-I.shape[0]/2.0
        H=np.dot(np.dot(T0,H0),T1)

        # transform each channel separately
        Icv=cv.fromarray(np.copy(I))
        I1cv=cv.CreateMat(I.shape[0],I.shape[1],Icv.type)

        cv.WarpPerspective(Icv,I1cv,cv.fromarray(np.copy(H)),fillval=1.0);
        I1=np.asarray(I1cv)
        I1[np.nonzero(I1<0)]=fillval
        return I1

def joinImages(I1,I2):
    newHeight = max(I1.shape[0],I2.shape[0])
    canvas = np.zeros((newHeight,I1.shape[1]+I2.shape[1]), dtype=I1.dtype)
    canvas[0:I1.shape[0],0:I1.shape[1]]=I1
    canvas[0:I2.shape[0],I1.shape[1]:canvas.shape[1]]=I2
    return canvas

def prepOpenCV(I):
    I = I + np.float32((np.random.random(I.shape) - .5)*.05)
    I[I>.99]=.99
    I[I<.01]=.01
    return I

def fastResize(I,rszFac,sig=-1):
    """ Resizes the input image I by factor 'rszFac'. 'rszFac' should be
    a float greater than 0.0, where smaller values leads to shrunken
    versions of I, and values greater than 1.0 lead to bigger-versions of
    I.
    Input:
        obj I: scipy img
        float rszFac:
    Output:
        A resized image Iout.
    """
    if rszFac==1:
        return I
    else:
        # Almost certain that this np.copy(I) is not necessary, since cv.Resize
        # will interpolate new pixel values in Iout. Removing np.copy(I) didn't
        # seem to affect results, and speeds things up. -- EK
        #Icv=cv.fromarray(np.copy(I))
        if not I.flags.c_contiguous:
            # numpy requires arrays be contiguous in memory - when you
            # pass it to OpenCV, then try to re-convert back to numpy,
            # you get an error in np.asarray if I isn't contiguous.
            I = np.copy(I) # Makes I contiguous
        Icv = cv.fromarray(I)
        I1cv=cv.CreateMat(int(math.floor(I.shape[0]*rszFac)),int(math.floor(I.shape[1]*rszFac)),Icv.type)
        cv.Resize(Icv,I1cv,interpolation=cv.CV_INTER_AREA)
        Iout = np.asarray(I1cv)
        if sig>0:
            Iout=gaussian_filter(Iout,sig);

        return Iout

def fastFlip(I):
    Icv=cv.fromarray(np.copy(I))
    I1cv=cv.CreateMat(I.shape[0],I.shape[1],Icv.type)
    cv.Flip(Icv,I1cv,-1)
    Iout=np.asarray(I1cv)
    return Iout

def estimateBg(I):
    """ Estimates the background-intensity value of I by histogramming
    the pixel intensity values of I into 10 buckets. Then, it takes
    the most-heavily populated bucket, and returns the lowest-intensity
    value of the range in that bucket (recall that hist-buckets range
    from [A,B]. estimateBg chooses A).
    """
    Ival = I
    Ival[np.isnan(Ival)] = 1
    Ihist = np.histogram(Ival,bins=10);
    return Ihist[1][np.argmax(Ihist[0])] # background
    #bucketIdx = np.argmax(Ihist[0])
    #a, b = Ihist[1][bucketIdx], Ihist[1][bucketIdx+1]
    #T = a
    #T = a + ((b-a)/2.0)
    #print "found {0}, old was {1}".format(T, Ihist[1][bucketIdx])
    #return T
    
def NCC(I,patch):
    I = prepOpenCV(I);
    patch = prepOpenCV(patch);
    patchCv=cv.fromarray(np.copy(patch))
    ICv=cv.fromarray(np.copy(I))
    outCv=cv.CreateMat(I.shape[0]-patch.shape[0]+1,I.shape[1]-patch.shape[1]+1,patchCv.type)
    cv.MatchTemplate(ICv,patchCv,outCv,cv.CV_TM_CCOEFF_NORMED)
    Iout=np.asarray(outCv)
    Iout[Iout==1.0]=0; # opencv bug
    outPad = np.ones(I.shape)*-1
    outPad[0:Iout.shape[0],0:Iout.shape[1]]=Iout
    return outPad
    
def variableDiffThr(I,patch):
    """ Image-difference metric between I, PATCH. Tries to filter out
    the unwanted effects of background by doing the following.
    """
    #estimate threshold for comparison: 
    try:
        Ibg = estimateBg(I);
        Pbg = estimateBg(patch);

        Ithr = (Ibg - I.min()) / 2
        Pthr = (Pbg - patch.min()) / 2
        thr = min(Ithr,Pthr)
        diff=np.abs(I-patch);
        # sum values of diffs above  threshold
        err = np.sum(diff[np.nonzero(diff>thr)])

    except Exception as e:
        print e
        traceback.print_exc()
        print "I.shape:", I.shape
        print "patch.shape:", patch.shape
        print "Ibg.shape:", Ibg.shape
        print "Pbg.shape:", Pbg.shape
        print "BOOM."
    return err


def padWithBorderHandling(M,i1exp,i2exp,j1exp,j2exp):
    Mpad = np.zeros((M.shape[0]+i1exp+i2exp,
                     M.shape[1]+j1exp+j2exp), dtype='float32')
    Mpad[i1exp:i1exp+M.shape[0],
         j1exp:j1exp+M.shape[1]] = M

    # fill corners if needed
    upleft_pixel = M[0,0]
    Mpad[0:i1exp,0:j1exp]=upleft_pixel
    upright_pixel = M[0,M.shape[1]-1]
    Mpad[0:i1exp,Mpad.shape[0]-1-j2exp:Mpad.shape[0]-1]=upright_pixel;
    botleft_pixel = M[M.shape[0]-1,0]
    Mpad[Mpad.shape[0]-1-i2exp:Mpad.shape[0]-1,0:j1exp]=botleft_pixel;
    botright_pixel = M[M.shape[0]-1,M.shape[1]-1]
    Mpad[Mpad.shape[0]-1-i2exp:Mpad.shape[0]-1,
         Mpad.shape[0]-1-j2exp:Mpad.shape[1]-1]=botright_pixel;

    # fill edges if needed
    leftedge = M[0:M.shape[0]-1,0]
    Mpad[i1exp:i1exp+leftedge.shape[0],0:j1exp]=np.tile(leftedge,(j1exp,1)).T

    rightedge = M[0:M.shape[0]-1,M.shape[1]-1]
    Mpad[i1exp:i1exp+rightedge.shape[0],
         Mpad.shape[1]-1-j2exp:Mpad.shape[1]-1]=np.tile(rightedge,(j2exp,1)).T

    topedge = M[0,0:M.shape[1]-1]
    Mpad[0:i1exp,j1exp:j1exp+topedge.shape[0]]=np.tile(topedge,(i1exp,1))

    botedge = M[M.shape[0]-1,0:M.shape[1]-1]
    Mpad[Mpad.shape[0]-1-i2exp:Mpad.shape[0]-1,
         j1exp:j1exp+botedge.shape[0]]=np.tile(botedge,(i2exp,1))

    return Mpad
'''
expand patch by pixPad with nans
'''
def lkSmallLarge(patch,I,i1,i2,j1,j2,pixPad=5, minArea=np.power(2, 17)):
    patchPad = np.empty((patch.shape[0]+2*pixPad,
                         patch.shape[1]+2*pixPad), dtype='float32')

    patchPad[:] = np.nan
    patchPad[pixPad:patch.shape[0]+pixPad,
             pixPad:patch.shape[1]+pixPad] = patch

    Ibg = estimateBg(I);
    IPad = Ibg * np.ones((I.shape[0]+2*pixPad,
                          I.shape[1]+2*pixPad), dtype='float32')

    IPad[pixPad:I.shape[0]+pixPad,
         pixPad:I.shape[1]+pixPad] = I
    
    Ic = IPad[i1:i2+2*pixPad,j1:j2+2*pixPad]

    IO=lk.imagesAlign(Ic,patchPad,trfm_type='rigid',fillval=Ibg, minArea=minArea)
    Ireg = IO[1]
    Ireg = Ireg[pixPad:patch.shape[0]+pixPad,
                pixPad:patch.shape[1]+pixPad]

    #err=np.sum(diff[np.nonzero(diff>.25)])
    err = variableDiffThr(Ireg,patch)
    diff=np.abs(Ireg-patch);
    return (err,diff,Ireg)

''' 
Input: 
  I0: full image
  bb: bounding box of patch (y1,y2,x1,x2)
  imList: list of full filenames for images to search
  threshold: only return matches above this value
  rszFac: downsampling factor for speed
  region: bounding box to limit search for speed (TODO) (y1,y2,x1,x2)
  bool output_Ireg: If True, then find_patch_matchesV1 will output the
      aligned image Ireg (this will consume more memory, caution).
  bool save_patches: If True, then this will save aligned output patch
      Ireg to disk, at directory OUTDIR.

Output:
  list of tuples, one for every match
  ((filename, score1, score2, patch, i1, i2, j1, j2, resize factor), (...) )

  score1: result from NCC. Higher is better. Ranges from [-1.0, 1.0].
  score2: produced from local alignment. this score is much more reliable.
          Lower is better. Ranges from [0.0, 1.0].

  You must scale (i1,i2,j1,j2) by resize factor, i.e. you should do:

  Example:
  i1 = int(round(i1 / rszFac))
  i2 = int(round(i2 / rszFac))
  j1 = int(round(j1 / rszFac))
  j2 = int(round(j2 / rszFac))
  I1cropped=I1[i1:i2,j1:j2]

'''
def find_patch_matchesV1(I,bb,imList,threshold=.8,rszFac=.75,bbSearch=None, 
                         bbSearches=None, padSearch=.75,padPatch=0.0,doPrep=True,
                         output_Ireg=False, jobid=None, save_patches=False, outdir=None, outid_start=0,
                         progress_queue=None):
    bb = list(bb)
    if bbSearch != None:
        bbSearch = list(bbSearch)
    if bbSearches != None:
        bbSearches = list(bbSearches)
    matchList = [] # (filename, left,right,up,down)
    if doPrep:
        I=prepOpenCV(I);
    if save_patches:
        try: os.makedirs(outdir)
        except: pass
    outid = outid_start # Used for save_patches
    I = np.round(fastResize(I,rszFac)*255.)/255;

    bb[0] = bb[0]*rszFac
    bb[1] = bb[1]*rszFac
    bb[2] = bb[2]*rszFac
    bb[3] = bb[3]*rszFac
    [bbOut,bbOff]=expand(bb[0],bb[1],bb[2],bb[3],I.shape[0],I.shape[1],padPatch)
    patchFoo = I[bbOut[0]:bbOut[1],bbOut[2]:bbOut[3]]

    patch = patchFoo[bbOff[0]:bbOff[1],bbOff[2]:bbOff[3]]

    if bbSearch != None:
        bbSearch[0] = bbSearch[0]*rszFac
        bbSearch[1] = bbSearch[1]*rszFac
        bbSearch[2] = bbSearch[2]*rszFac
        bbSearch[3] = bbSearch[3]*rszFac

    bestScore, bestMatch = None, None

    for cur_i, imP in enumerate(imList):
        if bbSearches != None:
            bbSearch = map(lambda c: c*rszFac, bbSearches[cur_i])
        I1 = standardImread(imP,flatten=True)
        if doPrep:
            I1=prepOpenCV(I1)
        I1 = np.round(fastResize(I1,rszFac)*255.)/255.

        # crop to region if specified
        if bbSearch != None:
            [bbOut1,bbOff1]=expand(bbSearch[0],bbSearch[1],
                                   bbSearch[2],bbSearch[3],
                                   I1.shape[0],I1.shape[1],padSearch)
            I1=I1[bbOut1[0]:bbOut1[1],bbOut1[2]:bbOut1[3]]

        patchCv=cv.fromarray(np.copy(patch))
        ICv=cv.fromarray(np.copy(I1))
        outCv=cv.CreateMat(I1.shape[0]-patch.shape[0]+1,I1.shape[1]-patch.shape[1]+1, cv.CV_32F)
        
        cv.MatchTemplate(ICv,patchCv,outCv,cv.CV_TM_CCOEFF_NORMED)
        Iout=np.asarray(outCv)
        
        Iout[Iout==1.0]=0; # opencv bug
        foundone = False
        while Iout.max() > threshold:
            foundone = True
            score1 = Iout.max() # NCC score
            YX=np.unravel_index(Iout.argmax(),Iout.shape)
            i1=YX[0]; i2=YX[0]+patch.shape[0]
            j1=YX[1]; j2=YX[1]+patch.shape[1]

            (err,diff,Ireg)=lkSmallLarge(patch,I1,i1,i2,j1,j2)
            score2 = err / diff.size # pixel reg score
            Ireg_out = Ireg if output_Ireg else None
            if save_patches:
                outpath = os.path.join(outdir, "{0}.png".format(outid))
                outid += 1
                misc.imsave(outpath, Ireg)
                Ireg_out = outpath

            if bbSearch != None:
                m = (imP,score1,score2,Ireg_out,
                     i1+bbOut1[0],i2+bbOut1[0],
                     j1+bbOut1[2],j2+bbOut1[2],rszFac)
            else:
                m = (imP,score1,score2,Ireg_out,
                     i1,i2,j1,j2,rszFac)
            matchList.append(m)
                
            if bestScore == None or score2 < bestScore:
                bestScore = score2
                bestMatch = m
            # mask out detected region
            i1mask = max(0,i1-patch.shape[0]/3)
            i2mask = min(Iout.shape[0],i1+patch.shape[0]/3)
            j1mask = max(0,j1-patch.shape[1]/3)
            j2mask = min(Iout.shape[1],j1+patch.shape[1]/3)
            Iout[i1mask:i2mask,j1mask:j2mask]=0

        if jobid != None and progress_queue != None:
            progress_queue.put(True)
        
    if not matchList:
        print "Warning - couldn't find any matches."
    return matchList

def matchAll(digit_hash,I):
    result_hash = {}
    for key in digit_hash.keys():
        patch = prepOpenCV(digit_hash[key]);
        patchCv=cv.fromarray(np.copy(patch))
        ICv=cv.fromarray(np.copy(I))
        outCv=cv.CreateMat(I.shape[0]-patch.shape[0]+1,I.shape[1]-patch.shape[1]+1,patchCv.type)
        cv.MatchTemplate(ICv,patchCv,outCv,cv.CV_TM_CCOEFF_NORMED)
        Iout=np.asarray(outCv)
        Iout[Iout==1.0]=0; # opencv bug
        result_hash[key]=Iout

    return result_hash

def stackMax(result_hash):
    maxSurf=np.zeros(1); symmax=-1;
    for key in result_hash.keys():
        out=result_hash[key]
        if out.max() > maxSurf.max():
            maxSurf = out
            symmax = key
            
    return (maxSurf,symmax)

def stackDel(match_hash,i1,i2,j1,j2):
    for key in match_hash.keys():
        out=match_hash[key]
        out[i1:i2,j1:j2]=0

def digitParse(digit_hash,imList,bbSearch,nDigits, do_flip=False):
    """Runs NCC-based OCR on the images on imList.
    Input:
        dict digit_hash: maps {str digit: img digit_exemplar}
        lst imList: list of imagepaths to search over
        bbSearch: [y1,y2,x1,x2] coords to search on
        nDigits: an integer that specifies how many digits there are.
        do_flip: If True, then flip the image.
    Output:
        A list of results of the form:
            [(imgpath_i, ocr_str_i, res_meta_i), ...)
        where res_meta_i is a tuple of len nDigits, containing:
            (y1,y2,x1,x2, str digit, obj digitimg, float score)
    """
    digitList = digit_hash.values();
    patchExample = digitList[0]

    results = []

    for imP in imList:
        I1 = standardImread(imP,flatten=True)
        if do_flip == True:
            I1 = fastFlip(I1)
        I1=prepOpenCV(I1)
        I1=I1[bbSearch[0]:bbSearch[1],bbSearch[2]:bbSearch[3]]
        # perform matching for all digits
        # return best matching digit
        # mask out 
        match_hash = matchAll(digit_hash,I1)
        # match_hash are dicts mapping {str digit: img}
        result_meta = []

        while len(result_meta) < nDigits:
            res=stackMax(match_hash)
            Iout=res[0]
            sym=res[1]
            YX=np.unravel_index(Iout.argmax(),Iout.shape)
            i1=YX[0]; 
            i2=YX[0]+digit_hash[sym].shape[0]
            j1=YX[1]; 
            j2=YX[1]+digit_hash[sym].shape[1]

            patch = digit_hash[sym]
            #(err,diff,Ireg)=lkSmallLarge(patch,I1,i1,i2,j1,j2)
            Ireg = I1[i1:i2,j1:j2]
            result_meta.append((i1,i2,j1,j2,sym,Ireg,Iout.max()))
            
            # mask out detected region
            i1mask = max(0,i1-digit_hash[sym].shape[0]/3)
            i2mask = min(Iout.shape[0],i1+digit_hash[sym].shape[0]/3)
            j1mask = max(0,j1-digit_hash[sym].shape[1]/3)
            j2mask = min(Iout.shape[1],j1+digit_hash[sym].shape[1]/3)
            stackDel(match_hash,i1mask,i2mask,j1mask,j2mask)

        # Sort resutl_list and crop out the digits
        result_meta=sorted(result_meta,key=lambda result_meta:result_meta[2])

        # crop out digits
        ocr_str=""
        for r in result_meta:
            ocr_str += r[4]
            
        results.append((imP,ocr_str,result_meta))

    return results

def numProcs():
    nProc=mp.cpu_count() 
    #nProc=1
    return nProc

def cropBb(I,bb):
    return I[bb[0]:bb[1],bb[2]:bb[3]]

def expand(i1,i2,j1,j2,iMx,jMx,pFac):
    # TODO: fix all refs to this function to use the Bbs version
    ''' Pad the rectangle from the input by factor pd. Return both the new rectangle and coordinates for extracting the unpadded rectangle from new padded, cropped one'''
    # don't allow the resulting image to take up more than 33% of the width
#    maxPd=round((min(iMx,jMx)/3.0)/2.0)
    pd=min(i2-i1,j2-j1)*pFac

    i1o=i1-pd; i1o=max(i1o,0);
    i2o=i2+pd; i2o=min(i2o,iMx)

    j1o=j1-pd; j1o=max(j1o,0);
    j2o=j2+pd; j2o=min(j2o,jMx)

    iOff=i1-i1o; jOff=j1-j1o;
    rOut=np.array([i1o,i2o,j1o,j2o])
    rOff=np.array([iOff,iOff+i2-i1,jOff,jOff+j2-j1])

    return (rOut,rOff)

def imsave(path,I):
    # assumed image is between 0 and 1
    I[0,0]=.01; I[1,0]=.99
    try:
        misc.imsave(path,I)
    except Exception as e:
        traceback.print_exc()
        print "    Path was:", path

def safeExpand(bb,pd,iMx,jMx):
    i1=bb[0]-pd; i1=max(i1,0);
    i2=bb[1]+pd; i2=min(i2,iMx)
    j1=bb[2]-pd; j1=max(j1,0);
    j2=bb[3]+pd; j2=min(j2,jMx)

    return np.array([i1,i2,j1,j2])
    
def expandBbsSingle(bb,iMx,jMx,pFac):

    iLen=bb[1]-bb[0]
    jLen=bb[3]-bb[2]
    # compute pad factor to smaller dimension
    pd=min(iLen,jLen)*pFac

    # compute new cropped region
    bbOut=safeExpand(bb,pd,iMx,jMx)

    # correct offsets of bb
    i1=bb[0]-bbOut[0]
    i2=i1+iLen
    j1=bb[2]-bbOut[2]
    j2=j1+jLen

    bbOff=np.array([i1,i2,j1,j2,bb[4]])
    return (bbOut,bbOff)
    

def expandBbsMulti(bbs,iMx,jMx,pFac):

    # compute pad factor to smaller dimension
    bb1=bbs[0,:]
    iLen=bb1[1]-bb1[0]
    jLen=bb1[3]-bb1[2]
    # compute pad factor to smaller dimension
    pd=min(iLen,jLen)*pFac

    bbSuper=bbUnion1(bbs)

    bbOut=safeExpand(bbSuper,pd,iMx,jMx)

    # compute super region
    # then pad super region
    # then compute offset to that

    bbsOff=np.zeros((0,5))
    for i in range(bbs.shape[0]):
        bb=bbs[i,:]
        i1=bb[0]-bbOut[0]
        i2=i1+iLen
        j1=bb[2]-bbOut[2]
        j2=j1+jLen
        bbsOff=np.vstack((bbsOff,np.array([i1,i2,j1,j2,bb[4]])))

    return (bbOut,bbsOff)


def expandBbs(bbs,iMx,jMx,pFac):
    ''' Assumed that bbs are all the same dim. Padding is relative to the size 
        one bb.
    Input:
        list bbs: List of bounding boxes
        int iMx: Maximum height
        int jMx: Maximum width
        int pFac: Amount by which to adjust padding.
    Output:
        list bbsOut: A new list of bounding boxes, but where each bb_i has 
                     been (safely) expanded.
        list bbsOff: A list of offsets required to go from coords in BBS
                     to coords in BBSOUT.
    '''
    # don't allow the resulting image to take up more than 33% of the width
    if len(bbs.shape)==1:
        return expandBbsSingle(bbs,iMx,jMx,pFac)
    else:
        return expandBbsMulti(bbs,iMx,jMx,pFac)


# extend bbUnion to take in a list of BBS
def bbUnion1(bbs):
    bbOut=[float('inf'),0,float('inf'),0]
    for i in range(bbs.shape[0]):
        bb1=bbs[i,:]
        bbOut[0]=min(bbOut[0],bb1[0])
        bbOut[1]=max(bbOut[1],bb1[1])
        bbOut[2]=min(bbOut[2],bb1[2])
        bbOut[3]=max(bbOut[3],bb1[3])
        
    return bbOut

def bbUnion(bb1,bb2):
    if len(bb1)==0:
        return bb2
    if len(bb2)==0:
        return bb1
        
    bbOut=[0,0,0,0]
    bbOut[0]=min(bb1[0],bb2[0])
    bbOut[1]=max(bb1[1],bb2[1])
    bbOut[2]=min(bb1[2],bb2[2])
    bbOut[3]=max(bb1[3],bb2[3])
    return bbOut

def csv2bbs(csvP):
    bdReader=csv.reader(open(csvP,'r'))
    isFirst=True; pFac=.1;
    bbs=np.empty((0,5))
    # loop over every target location
    for row in bdReader:
        if isFirst:
            isFirst=False;
            continue
        isContest=string.atoi(row[7]);
        if isContest==1:
            continue
        x1=string.atoi(row[2]); x2=x1+string.atoi(row[4]);
        y1=string.atoi(row[3]); y2=y1+string.atoi(row[5]);
        idx=string.atoi(row[1]);
        # expand region around target
        row1=np.array([y1,y2,x1,x2,idx])
        bbs=np.vstack((bbs,row1));
        
    return bbs;

def maskBordersTargets(I,bbs,pf=.05):
    return maskBorders(maskTargets(I,bbs,pf=pf),pf=pf);

def maskBorders(I,pf=.05):
    # to account for poorly scanned borders, create nan-padded Irefs
    IM=np.copy(I);
    rPd=pf*I.shape[0]; cPd=pf*I.shape[1];
    IM[1:rPd,:]=np.nan; IM[-rPd:,:]=np.nan;
    IM[:,1:cPd]=np.nan; IM[:,-cPd:]=np.nan;
    return IM

def maskTargets(I,bbs,pf=.05):
    ''' Set regions of targets to be NANs '''
    IM=np.copy(I);
    for i in range(bbs.shape[0]):
        y1=bbs[i,0]; y2=bbs[i,1]
        x1=bbs[i,2]; x2=bbs[i,3]        
        IM[y1:y2,x1:x2]=np.nan;        

    return IM

def resizeOrNot(shape, c, MIN_DIM=MIN_IMG_DIM):
    """ Given an image shape, and an integer 'c', returns the
    appropriate scaling factor required to make the largest
    dimension of 'shape' be at most 'c'.
    For instance, if shape is (500, 1000), and c is 800, then this
    outputs '0.8'. 
    If shape is (500, 1000), and c is 20, then this outputs
    '0.02'.
    Also makes sure that any dimension is at least MIN_DIM large,
    to avoid problems where skinny image patches get downsized to
    tiny 2x500 slivers, causing problems with image computation.
        shape: (500, 1000), c is 20, sc = '0.02'
        
    Input:
        tuple shape: (height, width)
        int c:
    Output:
        A suggested scale.
    """
    largestDim=max(shape[0:2])
    smallestDim = min(shape[0:2])
    if largestDim<c:
        # Don't want to grow the image.
        return 1.0
    scaleFactor = c / float(largestDim)
    minScaleFactor = MIN_DIM / float(smallestDim);
    return max(scaleFactor,minScaleFactor)

def rgb2gray(I):
    if len(I.shape)<3:
        return I
    else:
        Ichn1=I[:,:,0]
        Icv=cv.fromarray(np.copy(I))
        Ichn1cv=cv.fromarray(np.copy(Ichn1))
        cv.CvtColor(Icv,Ichn1cv,cv.CV_RGB2GRAY)
        Iout=np.asarray(Ichn1cv)
        return Iout

def arraySlice(A,inds):
    out=[]
    for i in inds:
        out.append(A[i])

    return out

def standardImread(fNm,flatten=False):
    Icv=cv.LoadImage(fNm);
    I=np.float32(np.asarray(Icv[:,:])/255.0)
    if flatten:
        I=rgb2gray(I)
    return I

def standardImread_v2(imgpath, flatten=False, dtype='float32', normalize=True):
    """ Reads in IMGPATH, and outputs a numpy array with pix. If normalize
    is True, then intensity values will be floats from [0.0, 1.0]. O.w.
    will be ints from [0, 255].
    """
    cvmode = cv.CV_LOAD_IMAGE_GRAYSCALE if flatten else cv.CV_LOAD_IMAGE_COLOR
    Icv = cv.LoadImageM(imgpath, cvmode)
    Inp = np.asarray(Icv, dtype=dtype)
    if normalize:
        Inp = Inp / 255.0
    return Inp

def remove_border_topleft(A):
    """ Removes black border from the top+left  of A - created due to
    the straightener adding padding to voted ballots.
    """
    h,w = A.shape
    out = np.zeros(A.shape, dtype=A.dtype)
    for i in xrange(h):
        thesum = np.sum(A[i])
        if thesum != 0:
            break
    for j in xrange(w):
        thesum = np.sum(A[:,j])
        if thesum != 0:
            break
    # i is the number of rows with all-black
    # j is the number of cols with all-black
    out[0:h-i, 0:w-j] = A[i:,j:]
    return out, i, j
