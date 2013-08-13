import cProfile
import numpy as np
import scipy.misc as misc
import math, traceback, pdb
try:
    import cPickle as pickle
except ImportError as e:
    import pickle
import time
import cv, cv2
import shared as sh
from scipy.ndimage import gaussian_filter
import matplotlib.pyplot as plt

#@profile
def imagesAlign1(I,Iref,H0=np.eye(3,dtype=np.float32),
                 trfm_type='similarity',verbose=False, minArea = np.power(2, 11)):
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
    lbda=1e-6
    wh=Iref.shape
    eps=1e-3
    sig=2

    # recursive check
    if np.prod(wh)<minArea:
        H=H0
    else:
        I1=sh.fastResize(I,.5)
        Iref1=sh.fastResize(Iref,.5)
        S=np.eye(3); S[0,0]=2; S[1,1]=2;
        H0=np.dot(np.dot(np.linalg.inv(S),H0),S)
        (H,errx)=imagesAlign1(I1,Iref1,H0=H0,trfm_type=trfm_type,verbose=verbose, minArea=minArea)
        H=np.dot(S,np.dot(H,np.linalg.inv(S)))


    # smooth images
    Iref=gaussian_filter(Iref,sig)
    I=gaussian_filter(I,sig)

    # pad image with NaNs
    ws=np.concatenate(([0],[0],range(wh[0]),[wh[0]-1],[wh[0]-1]))
    hs=np.concatenate(([0],[0],range(wh[1]),[wh[1]-1],[wh[1]-1]))
    try:
        Iref=Iref[np.ix_(ws,hs)]
        I=I[np.ix_(ws,hs)]
    except Exception as e:
        traceback.print_exc()
        print '...Iref.shape:', Iref.shape
        print '...I.shape:', I.shape
        misc.imsave("_Iref_{0}.png".format(str(t)), Iref)
        misc.imsave("_I_{0}.png".format(str(t)), I)
        raise e
    hs=np.array([0,1,wh[1]+2,wh[1]+3])
    ws=np.array([0,1,wh[0]+2,wh[0]+3])

    Iref[ws,:]=np.nan; I[ws,:]=np.nan;
    Iref[:,hs]=np.nan; I[:,hs]=np.nan;
    
    wts=np.array([1,1,1.0204,.03125,1.0313,.0204,.000555,.000555]);
    s=math.sqrt(Iref.size)/128.0
    wts[2]=math.pow(wts[2],1/s)
    wts[3]=wts[3]/s
    wts[4]=math.pow(wts[4],1/s)
    wts[5]=wts[5]/s
    wts[6]=wts[6]/(s*s)
    wts[7]=wts[7]/(s*s)

    # compute differences

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
    HH=ds2H(-1*np.ones(8),wts)
    Hs=HH[1][keep,:]

    # apply transformations
    Ts=np.zeros([Hs.shape[0],Iref.shape[0],Iref.shape[1]])
    Ms=np.ones([Iref.shape[0],Iref.shape[1]],dtype=np.float32)
    
    for i in range(Hs.shape[0]):
        Ts[i,:,:]=sh.imtransform(Iref,Hs[i,:,:])
        Ms=Ms * (np.float32(~np.isnan(Ts[i,:,:])))

    Ds=Ts-np.tile(Iref,[Hs.shape[0],1,1])
    D=Ds.reshape(Ds.shape[0],np.prod(Iref.shape))
    Lbda=lbda*np.prod(Iref.shape)*np.eye(Ds.shape[0])
    err=np.Inf
    ds=np.zeros([8,1])

    for i in xrange(100):
        # warp image with current esimate
        Ip=sh.imtransform(I,H)
        M=Ms * np.float32(~np.isnan(Ip) & ~np.isnan(Iref))
        Mf=M.reshape(I.size,1)
        dI=Ip-Iref; dIf=dI.reshape(np.prod(I.shape),1)

        # guard against bad things
        if np.sum(Mf) < 2:
            H = np.eye(3)
            err = np.Inf
            break

        # check if > half of pixels turn to NAN
        # subtract new nans from old nans, divide by old valids
        origValidPixels=np.sum(1-(np.isnan(I)+0))
        newValidPixels=np.sum(1-(np.isnan(Ip+I)+0))
        if newValidPixels<(origValidPixels/3.):
            return (np.eye(3),np.inf)

        
        #=== CODE PRIOR TO REFACTOR ===
        idx=np.nonzero(np.squeeze(Mf))
        D_valid=D[:,idx]
        D0=np.squeeze(D_valid);
        dI1=dIf[idx]
        _A = np.dot(D0, D0.T)
        _B = np.linalg.inv(_A + Lbda)
        _C = np.dot(D0, dI1)
        ds1 = np.dot(_B, _C)

        #ds1=np.dot(np.linalg.inv(np.dot(D0,D0.T)+Lbda),np.dot(D0,dI1))
        ds[keep]=ds1;
        ds = np.squeeze(ds)
        HH=ds2H(ds,wts); H=np.dot(H,HH[0]); H=H/H[2,2]
        err0=err; err=np.abs(dI1); err=np.mean(err); delta=err0-err;
        if verbose:
            print I.shape," i=",i," err=",err," del=",delta
        if delta<eps:
            break
    return (H,err)

def ds2H(ds,wts):
    Hs=np.eye(3)
    Hs=np.tile(Hs,[8,1,1])
    # 1. x translation
    Hs[0,0,2]=wts[0]*ds[0]
    # 2. y translation
    Hs[1,1,2]=wts[1]*ds[1]
    # 3. scale
    Hs[2,:2,:2]=np.eye(2)*math.pow(wts[2],ds[2])
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
    H=np.eye(3)
    for i in range(Hs.shape[0]):
        H=np.dot(Hs[i,:,:],H)

    return (H,Hs)

def imagesAlign1_profile(I,Iref,H0=np.eye(3,dtype=np.float32),
                 trfm_type='similarity',verbose=False, minArea = np.power(2, 11)):
    # TODO: fix this!
    #cProfile.run('(H,err)=imagesAlign1(I,Iref)', 'profile_imagesalign1')
    cProfile.runctx('(H,err)=imagesAlign1(I,Iref)', globals(), locals(), filename='profile_imagesalign1')
    return (H,err)
