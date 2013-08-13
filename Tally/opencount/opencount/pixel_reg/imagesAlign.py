import cProfile
from imagesAlign1_cy import imagesAlign1
import numpy as np
import scipy.misc as misc
import math, traceback, pdb
try:
    import cPickle as pickle
except ImportError as e:
    import pickle
import time
import cv
import shared as sh
from scipy.ndimage import gaussian_filter

def imagesAlign(I,Iref,fillval=np.nan,trfm_type='similarity',
                vCells=1,hCells=1,rszFac=1,verbose=False,
                minArea = np.power(2, 11), applyWarp=True):
    """ Aligns I to IREF.
    Input:
        np.array I: Image you want to align. I must be larger than IREF.
        np.array Iref: Image you want to align against.
        int fillval: 
        str trfm_type: What image transformation to solve for. They are (in
            order of complexity): 'translation', 'rigid', 'similarity',
            'affine', and 'projective'. A nice page that describes
            these are at: 
                http://homepages.inf.ed.ac.uk/rbf/HIPR2/affine.htm
        int vCells, hCells: Params to allow aligning subcells of the 
            image, followed by stitching. Appears to rarely be used.
        float rszFac: Amount by which to scale the image - for
            performance, you want to scale down (i.e. 0.75).
        applyWarp: Causes imagesAlign to apply the found transformation
        to the input image I and return it. Without applyWarp, the function
        will only return the transformation matrix. This is used when
        cropped images are passed to the function, so the warp should not
        yet be applied to the cropped image but rather the original image,
        which is now the responsibility of the caller.
    Output:
        (H, Ireg, err). H is the transformation matrix that was found
        to best align I to Iref. Ireg is the result of aligning I to
        Iref. err is the alignment error.
    """
    if len(I.shape)==3:
        I1=sh.rgb2gray(I)
    else:
        I1=I
        
    if len(Iref.shape)==3:
        Iref1=sh.rgb2gray(Iref)
    else:
        Iref1=Iref

    WARN_USER, ORIG_DTYPE = False, None
    if I1.dtype != 'float32':
        WARN_USER, ORIG_DTYPE = True, I1.dtype
        I1 = I1.astype('float32')
    if Iref1.dtype != 'float32':
        WARN_USER, ORIG_DTYPE = True, Iref1.dtype
        Iref1 = Iref1.astype('float32')
    if WARN_USER:
        print "(Info) imagesAlign was called with input image dtype={0}. \
imagesAlign expects image dtype='float32' (Also, intensity vals in range \
[0.0,1.0]. The image dtype conversion was \
automatically done, but this slows down the computation a little. Consider \
trying to work in 'float32' in the first place if convenient for a little \
speed boost.".format(ORIG_DTYPE)

    t1 = time.clock()
    # check if more than one vertical and horizontal cell
    if (vCells>1) and (hCells>1):
        I2=imagesAlign(I1,Iref1,trfm_type=trfm_type, minArea=minArea)[1];
        Iout=np.copy(Iref1);
        pFac=.25;
        vStep=math.ceil(I1.shape[0]/vCells); vPad=pFac*vStep;
        hStep=math.ceil(I1.shape[1]/hCells); hPad=pFac*vStep;
        for i in range(vCells):
            for j in range(hCells):
                # 2. chop + pad each cell then align
                # 3. stitch back together
                i1=i*vStep; i1=max(i1,0);
                i2=(i+1)*vStep; i2=min(i2,I1.shape[0]-1);
                j1=j*hStep; j1=max(j1,0);
                j2=(j+1)*hStep; j2=min(j2,I1.shape[1]-1);

                i1p=i1-vPad; i1p=max(i1p,0);
                i2p=i2+vPad; i2p=min(i2p,I1.shape[0]-1);
                j1p=j1-hPad; j1p=max(j1p,0);
                j2p=j2+hPad; j2p=min(j2p,I1.shape[1]-1);
                
                Ic=I2[i1p:i2p,j1p:j2p]
                Irefc=Iref1[i1p:i2p,j1p:j2p]
                (H,err)=imagesAlign1(Ic,Irefc,trfm_type=trfm_type,verbose=verbose, minArea=minArea)
                IcT=sh.imtransform(Ic, H)
                Iout[i1:i2,j1:j2]=IcT[i1-i1p:(i1-i1p)+(i2-i1),j1-j1p:(j1-j1p)+(j2-j1)]

        return (np.eye(3),Iout,-1)

    if rszFac==1:
        t0 = time.clock()
        (H,err)=imagesAlign1(I1,Iref1,trfm_type=trfm_type,verbose=verbose, minArea=minArea)
        if verbose:
            print 'alignment time:',time.clock()-t0,'(s)'

        #print 'alignment time:',time.clock()-t0,'(s)'            
    else:
        I1=sh.fastResize(I1,rszFac)
        Iref1=sh.fastResize(Iref1,rszFac)
        S=np.eye(3, dtype=np.float32);
        S[0,0]=1/rszFac; S[1,1]=1/rszFac;
        H0=np.eye(3, dtype=np.float32)
        H0=np.dot(np.dot(np.linalg.inv(S),H0),S)
        t0 = time.clock()
        (H,err)=imagesAlign1(I1,Iref1,H0=H0,trfm_type=trfm_type,verbose=verbose, minArea=minArea)
        if verbose:
            print 'alignment time:',time.clock()-t0,'(s)'

        #print 'alignment time:',time.clock()-t0,'(s)'
        H=np.dot(S,np.dot(H,np.linalg.inv(S)))

    #print "overall time: ", time.clock() - t1
    if applyWarp:
        return (H,sh.imtransform(I,H,fillval=fillval),err)
    else:
        return (H,err)

def pttransform(I,H0,pt0):
    # transform point using center as origin
    T0=np.eye(3); T0[0,2]=I.shape[1]/2.0; T0[1,2]=I.shape[0]/2.0
    T1=np.eye(3); T1[0,2]=-I.shape[1]/2.0; T1[1,2]=-I.shape[0]/2.0
    H=np.dot(np.dot(T0,H0),T1)

    pt1=np.dot(H,pt0)
    pt1[0]=pt1[0]/pt1[2]; pt1[1]=pt1[1]/pt1[2]; pt1[2]=1

    return pt1


def associateTwoPage(tplImL, balImL):
    # return permuted balImL list
    # check first template against both ballots
    # Assumes that tplImL, balImL are ordered by imageorder, meaning:
    #   tplImL := [frontpath, backpath]
    #   balImL := [frontback, backpath]
    tpl0=tplImL[0]; tpl1=tplImL[1]
    bal0=balImL[0]; bal1=balImL[1]

    res0=checkBallotFlipped(bal0,tpl0)
    res1=checkBallotFlipped(bal1,tpl0)
    if res0[2]<res1[2]:
        return (res0,checkBallotFlipped(bal1,tpl1),(0,1))
    else:
        return (res1,checkBallotFlipped(bal0,tpl1),(1,0))

def checkBallotFlipped(I,Iref,verbose=False):
    rszFac=sh.resizeOrNot(I.shape,sh.FLIP_CHECK_HEIGHT)
    Iref1=sh.fastResize(Iref,rszFac)
    I1=sh.fastResize(I,rszFac)
    IR=sh.fastFlip(I1)
    (H,Io,err)=imagesAlign(I1,Iref1,trfm_type='translation')
    (HR,IoR,errR)=imagesAlign(IR,Iref1,trfm_type='translation')
    
    if(verbose):
        print 'flip margin: ', err, errR
        
    if err>errR:
        return (True, sh.fastFlip(I),errR);
    else:
        return (False, I, err);
