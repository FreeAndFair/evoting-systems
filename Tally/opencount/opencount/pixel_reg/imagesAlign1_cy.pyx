# cython: profile=False
# cython: boundscheck=False
# cython: wraparound=False

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

cimport numpy as np
DTYPE = np.float32
ctypedef np.float32_t DTYPE_t

def imagesAlign1(np.ndarray[DTYPE_t, ndim=2] I,
                 np.ndarray[DTYPE_t, ndim=2] Iref,
                 np.ndarray[DTYPE_t, ndim=2] H0=np.eye(3, dtype=DTYPE),
                 trfm_type='similarity',verbose=False, float minArea=np.power(2,11)):
    """
    Input:
        nparray I: Assumes that I is larger than IREF
        nparray Iref:
        nparray H0: Trans. mat.
        str trfm_type: Transformation trfm_type.
        int minArea: The minimum area that IREF is allowed to be - if 
            IREF.width*IREF.height is greater than this, then imagesAlign1
            will shrink both I and IREF by 50% until the area < MINAREA.
            Smaller values of MINAREA allow higher tolerance for wider
            translations, yet can lead to less-predictable results.
            Suggestion: For coarse global alignment, try smaller values
            of MINAREA. For finer local alignment, use larger MINAREA.
    """

    if minArea == None:
        #minArea = np.power(2, 15)
        minArea = np.power(2, 11)

    # declare types for all variables in function
    cdef float lbda=1e-6
    cdef int wh0, wh1
    cdef float eps=1e-3
    cdef float sig=2

    cdef np.ndarray[DTYPE_t, ndim=2] H, HH0
    cdef np.ndarray[DTYPE_t, ndim=3] HH1
    cdef np.ndarray[DTYPE_t, ndim=2] S    
    cdef np.ndarray[DTYPE_t, ndim=2] I1
    cdef np.ndarray[DTYPE_t, ndim=2] Iref1
    
    cdef np.ndarray[DTYPE_t, ndim=3] Ts, Ds
    cdef np.ndarray[DTYPE_t, ndim=2] Ms, D, Lbda, ds, D_zerod

    cdef np.ndarray[DTYPE_t, ndim=2] M, Mf, Ip, dI, dIf, dI1
    cdef np.ndarray[DTYPE_t, ndim=2] Mf_stacked, D0_masked
    cdef np.ndarray[DTYPE_t, ndim=2] _A_masked, _B_masked, _C_masked
    
    cdef DTYPE_t errx, err, err0, s, delta
    cdef DTYPE_t origValidPixels, newValidPixels
    cdef np.ndarray[DTYPE_t, ndim=1] wts

    cdef np.ndarray[np.int_t, ndim=1] ws, hs

    wh0=Iref.shape[0]
    wh1=Iref.shape[1]    
    # recursive check
    if (wh0*wh1)<minArea:
        H=H0
    else:
        I1=sh.fastResize(I,.5)
        Iref1=sh.fastResize(Iref,.5)
        S=np.eye(3,dtype=DTYPE); S[0,0]=2; S[1,1]=2;
        H0=np.dot(np.dot(np.linalg.inv(S),H0),S)
        (H,errx)=imagesAlign1(I1,Iref1,H0=H0,trfm_type=trfm_type,verbose=verbose, minArea=minArea)
        H=np.dot(S,np.dot(H,np.linalg.inv(S)))

    # smooth images
    Iref=gaussian_filter(Iref,sig)
    I=gaussian_filter(I,sig)

    # pad image with NaNs
    ws=np.concatenate(([0],[0],range(wh0),[wh0-1],[wh0-1]))
    hs=np.concatenate(([0],[0],range(wh1),[wh1-1],[wh1-1]))
    try:
        Iref=Iref[np.ix_(ws,hs)]
        I=I[np.ix_(ws,hs)]
    except Exception as e:
        traceback.print_exc()
        print '...Iref.shape:', Iref.shape[0], ' ', Iref.shape[1]
        print '...I.shape:', I.shape[0], ' ', I.shape[1]
        #misc.imsave("_Iref_{0}.png".format(str(t)), Iref)
        #misc.imsave("_I_{0}.png".format(str(t)), I)
        raise e
    ws=np.array([0,1,wh0+2,wh0+3])
    hs=np.array([0,1,wh1+2,wh1+3])

    Iref[ws,:]=np.nan; I[ws,:]=np.nan;
    Iref[:,hs]=np.nan; I[:,hs]=np.nan;
    
    wts=np.array([1,1,1.0204,.03125,1.0313,.0204,.000555,.000555], dtype=DTYPE);
    s=math.sqrt(Iref.size)/128.0
    wts[2]=math.pow(wts[2],1/s)
    wts[3]=wts[3]/s
    wts[4]=math.pow(wts[4],1/s)
    wts[5]=wts[5]/s
    wts[6]=wts[6]/(s*s)
    wts[7]=wts[7]/(s*s)

    if trfm_type=='translation':
        keep=[0,1];
    elif trfm_type=='rigid':
        keep=[0,1,5];
    elif trfm_type=='similarity':
        keep=[0,1,2,5];
    elif trfm_type=='affine':
        keep=[0,1,2,3,4,5];
    elif trfm_type=='projective':
        keep=[0,1,2,3,4,5,6,7];
                
    # compute transformations
    HH0,HH1=ds2H(-1*np.ones(8, dtype=DTYPE),wts)
    Hs=HH1[keep,:]

    # apply transformations
    Ts=np.zeros([Hs.shape[0],Iref.shape[0],Iref.shape[1]],dtype=DTYPE)
    Ms=np.ones([Iref.shape[0],Iref.shape[1]],dtype=DTYPE)
    for i in range(Hs.shape[0]):
        Ts[i,:,:]=sh.imtransform(Iref,Hs[i,:,:])
        Ms=Ms * (DTYPE(~np.isnan(Ts[i,:,:])))
    
    Ds=Ts-np.tile(Iref,[Hs.shape[0],1,1])
    D=Ds.reshape(Ds.shape[0],Iref.shape[0]*Iref.shape[1])
    Lbda=lbda*Iref.shape[0]*Iref.shape[1]*np.eye(Ds.shape[0], dtype=DTYPE)
    err=DTYPE(np.Inf)
    ds=np.zeros([8,1],dtype=DTYPE)

    D_zerod=np.nan_to_num(Ds.reshape(Ds.shape[0],Iref.size))
    origValidPixels=np.sum(1-(np.isnan(I)+0))

    for i in xrange(100):
        # warp image with current esimate
        Ip=sh.imtransform(I,H)
        M=Ms * DTYPE(~np.isnan(Ip) & ~np.isnan(Iref))
        Mf=M.reshape(I.shape[0]*I.shape[1],1)
        dI=Ip-Iref; dIf=dI.reshape(I.shape[0]*I.shape[1],1)

        # guard against bad things
        if np.sum(Mf) < 2:
            H = np.eye(3,dtype=DTYPE)
            err = DTYPE(np.Inf)
            break

        # check if > half of pixels turn to NAN
        # subtract new nans from old nans, divide by old valids
        newValidPixels=np.sum(1-(np.isnan(Ip+I)+0))
        if newValidPixels<(origValidPixels/3.):
            return (np.eye(3,dtype=DTYPE),DTYPE(np.inf))

        # NEW: apply mask via multiply rather than index
        Mf_stacked = np.tile(Mf.T,(D.shape[0],1))
        D0_masked = np.multiply(D_zerod,Mf_stacked)
        dI1 = np.nan_to_num(np.multiply(dIf,Mf))
        _A_masked = np.dot(D0_masked, D0_masked.T)
        _B_masked = np.linalg.inv(_A_masked + Lbda)
        _C_masked = np.dot(D0_masked, dI1)
        ds[keep]=np.dot(_B_masked, _C_masked)

        HH0,HH1=ds2H(np.squeeze(ds),wts); H=np.dot(H,HH0); H=H/H[2,2]
        err0=err; err=DTYPE(np.mean(np.abs(dI1)))
        delta=err0-err;
        if verbose:
            print I.shape[0], ' ',I.shape[1]," i=",i," err=",err," del=",delta
        if delta<eps:
            break
    return (H,err)

def ds2H(np.ndarray[DTYPE_t, ndim=1] ds,
         np.ndarray[DTYPE_t, ndim=1] wts):

    cdef np.ndarray[DTYPE_t, ndim=3] Hs
    cdef np.ndarray[DTYPE_t, ndim=2] H
    cdef DTYPE_t st, ct

    Hs=np.tile(np.eye(3,dtype=DTYPE),[8,1,1])
    # 1. x translation
    Hs[0,0,2]=wts[0]*ds[0]
    # 2. y translation
    Hs[1,1,2]=wts[1]*ds[1]
    # 3. scale
    Hs[2,:2,:2]=np.eye(2,dtype=DTYPE)*math.pow(wts[2],ds[2])
    # # # 4. shear
    Hs[3,0,1]=wts[3]*ds[3]    
    # # 5. scale non-uniform
    Hs[4,1,1]=math.pow(wts[4],ds[4])
    # # 6. rotation z
    ct=math.cos(wts[5]*ds[5]); st=math.sin(wts[5]*ds[5])
    Hs[5,:2,:2]=np.array([[ct,st],[-st,ct]])
    # # 7. rotation x
    ct=math.cos(wts[6]*ds[6]); st=math.sin(wts[6]*ds[6])    
    Hs[6,1,1]=ct; Hs[6,1,2]=-st;
    Hs[6,2,1]=st; Hs[6,2,2]=ct;
    # # 8. rotation y
    ct=math.cos(wts[7]*ds[7]); st=math.sin(wts[7]*ds[7])
    Hs[7,0,0]=ct; Hs[7,0,2]=-st;
    Hs[7,2,0]=st; Hs[7,2,2]=ct;    
    
    # collect into H
    H=np.eye(3,dtype=DTYPE)
    for i in range(Hs.shape[0]):
        H=np.dot(Hs[i,:,:],H)

    return (H,Hs)
