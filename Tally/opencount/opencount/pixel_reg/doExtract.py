import sys, pdb
from os.path import join as pathjoin
import shared as sh
from imagesAlign import *
import traceback, time
import os
import multiprocessing as mp
from wx.lib.pubsub import Publisher
import wx
from util import create_dirs
import pickle
import shutil
import array

from matplotlib.pyplot import show, imshow, figure, title

sys.path.append('..')
import global_align.global_align as global_align

# Consider only the middle of the "Fill in the Arrow" voting targets
# that Sequoia-style (e.g. SantaCruz) has. This is present because I
# don't want to re-do select targets.
# Note: This has not been used in quite some time. It should be safe
#       to remove this when cleaning up.
HACK_SANTACRUZ = False

# Global Alignment Method flags.
GALIGN_NORMAL = 42
GALIGN_CV     = 43

# Local Alignment Method flags.
LALIGN_NORMAL = 42
LALIGN_CV     = 43
LALIGN_NONE   = 44

def extractTargets(I,Iref,bbs,verbose=False):
    ''' Perform local alignment around each target, then crop out target  '''
    # Note: Currently only used in debugWorker. See extractTargetsRegions
    #       for the function actually used.
    rszFac=sh.resizeOrNot(I.shape,sh.COARSE_BALLOT_REG_HEIGHT)
    #IrefM=sh.maskBordersTargets(Iref,bbs);
    IrefM = Iref # Currently don't mask out targets, found it helps global alignment
    t0=time.clock();
    
    H1, I1, err = imagesAlign(I,IrefM,fillval=1,trfm_type='translation',rszFac=rszFac)
    if(verbose):
        print 'coarse align time = ',time.clock()-t0,'(s)'

    result = []
    pFac=7;

    for i in range(bbs.shape[0]):
        bb1=bbs[i,:]
        iLen=bb1[1]-bb1[0]
        jLen=bb1[3]-bb1[2]
        (bbOut,bbOff)=sh.expandBbs(bb1,I.shape[0],I.shape[1],pFac)

        Ic=sh.cropBb(I1,bbOut)
        IrefcNOMASK=sh.cropBb(Iref,bbOut)
        Irefc=sh.cropBb(IrefM,bbOut)

        rszFac=sh.resizeOrNot(Ic.shape,sh.LOCAL_PATCH_REG_HEIGHT)
        Hc1, Ic1, err = imagesAlign(Ic,Irefc,fillval=1,rszFac=rszFac,trfm_type='rigid')

        targ=np.copy(sh.cropBb(Ic1,bbOff))

        # unwind the transformations to get the global location of the target
        rOut_tr=pttransform(I,np.linalg.inv(H1),np.array([bbOut[2],bbOut[0],1]))
        rOff_tr=pttransform(Ic,np.linalg.inv(Hc1),np.array([bbOff[2],bbOff[0],1]))
        targLocGl=np.zeros(4)
        targLocGl[0]=round(rOut_tr[1]+rOff_tr[1])
        targLocGl[1]=round(rOut_tr[1]+rOff_tr[1]+iLen)
        targLocGl[2]=round(rOut_tr[0]+rOff_tr[0])
        targLocGl[3]=round(rOut_tr[0]+rOff_tr[0]+jLen)

        # weird bug in imsave where if the matrix is all ones, it saves as pure black
        targ[0,0]=.99
        result.append((bbs[i,4],targ,map(int,tuple(targLocGl)),err))
        #result.append((bbs[i,4],targ,map(int,tuple(targLocGl)),Idiff,Ic1))
        
    if(verbose):
        print 'total extract time = ',time.clock()-t0,'(s)'

    return result

def bbsInCell(bbs,i1,i2,j1,j2):
    """ Given a list of bbs, and a box (i1,i2,j1,j2), return all bbs in
    BBS whose center lies within (I1,I2,J1,J1).
    Output:
        An NxM dimension array, where N is the number of bbs that satisfy
        the criterion.
    """
    bbOut=np.zeros((0,5))
    for bb in bbs:
        iCtr=(bb[0]+bb[1])/2.
        jCtr=(bb[2]+bb[3])/2.        
        if (iCtr>=i1) and (iCtr<=i2) and (jCtr>=j1) and (jCtr<=j2):
            bbOut=np.vstack((bbOut,bb))

    return bbOut

def cropout_stuff(I, top, bot, left, right):
    h, w = I.shape
    x1 = int(round(left*w))
    y1 = int(round(top*h))
    x2 = int(round(w - (right*w)))
    y2 = int(round(h - (bot*h)))
    Inew = I[y1:y2, x1:x2]
    return np.copy(Inew)

def correctH(I, H0):
    T0=np.eye(3); T0[0,2]=I.shape[1]/2.0; T0[1,2]=I.shape[0]/2.0
    T1=np.eye(3); T1[0,2]=-I.shape[1]/2.0; T1[1,2]=-I.shape[0]/2.0
    H=np.dot(np.dot(T0,H0),T1)
    return H

def extractTargetsRegions(I,Iref,bbs,vCells=4,hCells=4,verbose=False,balP=None,
                          do_grid_opt=False, do_local_align=True,
                          method_galign=GALIGN_NORMAL, method_lalign=LALIGN_NORMAL):
    """ Given an image I (voted) and a ref image Iref (blank), extracts
    boundingboxes given by BBS from I, performing local image alignment
    between I and Iref.
    Input:
        bool DO_GRID_OPT:
            If True, then this will grid up the image into VCELLSxHCELLS
            cells. For each cell C_i, a super-region R is computed around 
            all voting targets T that reside in C_i, and a single local-alignment
            is performed for T. 
            If False, then a small area around each individual voting 
            target is aligned.
        int METHOD_GALIGN:
            Specifies which global alignment scheme to use. One of:
                GALIGN_NORMAL, GALIGN_CV
        int METHOD_LALIGN:
            Specifies which local alignment scheme to use. One of:
                LALIGN_NORMAL, LALIGN_CV, LALIGN_NONE
    Output:
        [(int targetID, nparray img, tuple bbImgLoc, float err), ...]
        IMG will always have a dtype=uint8 in range [0,255]
    """
    ''' Perform local alignment around each target, then crop out target  '''
    # 0.) Mask out targets on Iref, coarsely-align I to Iref.
    rszFac=sh.resizeOrNot(I.shape,sh.COARSE_BALLOT_REG_HEIGHT)
    #IrefM=sh.maskBordersTargets(Iref,bbs,pf=0.05)
    IrefM = Iref # Currently don't mask out targets, found it helps global alignment
    #IrefM_crop = cropout_stuff(IrefM, 0.05, 0.05, 0.05, 0.05)
    #Icrop = cropout_stuff(I, 0.05, 0.05, 0.05, 0.05)
    t0=time.clock()

    # GlobalAlign (V1): Simple scheme.
    #H1, I1, err = imagesAlign(Icrop, IrefM_crop, fillval=1, trfm_type='rigid', rszFac=0.25)
    #I1 = imtransform(I, H1)

    #orig_err = np.mean(np.abs(I - IrefM).flatten()) # L1 error, normalized by area
    orig_err = 9999999999.0 # effectively disable the below UNDO_GALIGN scheme
    if method_galign == GALIGN_NORMAL:
        ERR_REL_THR = 1.44 # 5 std devs. from santacruz1000 empirical
        H1, I1, err_galign = global_align.align_image(I, IrefM, crop=True, 
                                                      CROPX=0.05, CROPY=0.05,
                                                      MINAREA=np.power(2, 16))
        err_rel = err_galign / orig_err if orig_err != 0 else 0.0
    else:
        ERR_REL_THR = 2.0
        H1, I1, err_galign = global_align.align_cv(I, IrefM, computeErr=True, 
                                                   rmBlkBorder=True, fullAffine=False,
                                                   doSmooth=True, smooth_sigma=12)
        H1_ = np.eye(3, dtype=H1.dtype)
        H1_[:2,:] = H1
        H1 = H1_ # align_image outputs 3x3 H, but align_cv outputs 2x3 H.
        err_rel = err_galign / orig_err if orig_err != 0 else 0.0

    #misc.imsave("Iglobal.png", I1+IrefM)

    FLAG_UNDO_GALIGN = err_rel >= ERR_REL_THR
    #print 'err_galign={0:.5f}  err_orig={1:.5f}  ratio={2:.5f}'.format(err_galign, orig_err, err_rel)
    if FLAG_UNDO_GALIGN:
        print "(Info) Undoing galign (err_rel={0}) [wrote: undo_galign.log]".format(err_rel)
        f = open('undo_galign.log', 'a')
        print >>f, "balP={0}, orig_err={1}, err_galign={2}, err_rel={3}".format(balP,orig_err,err_galign,err_rel)
        f.close()
        H1 = np.eye(3, dtype=H1.dtype)
        I1 = I
        err_galign = orig_err
        
    if(verbose):
        print 'coarse align time = ',time.clock()-t0,'(s)'
    result = []
    pFac=7
    balname = os.path.split(balP)[-1]
    if method_lalign == LALIGN_NONE:
        for i, bb in enumerate(bbs):
            # bb := [i1, i2, j1, j2, targetID]
            target = I1[bb[0]:bb[1], bb[2]:bb[3]]
            if method_galign == GALIGN_NORMAL:
                target = np.round(target * 255.0).astype('uint8')
            result.append((bb[4], target, map(int, bb[:-1]), err_galign))
    elif not do_grid_opt:
        # 1.) Around each bb in BBS, locally-align I_patch to Iref_patch,
        #     then extract bb.
        for i, bb in enumerate(bbs):
            # bb := [i1, i2, j1, j2, targetID]
            bbExp, bbOff = sh.expandBbsSingle(bb, I1.shape[0], I1.shape[1], pFac)
            I_patch = I1[bbExp[0]:bbExp[1], bbExp[2]:bbExp[3]]
            IrefM_patch = IrefM[bbExp[0]:bbExp[1], bbExp[2]:bbExp[3]]
            rszFac = sh.resizeOrNot(I_patch.shape, sh.LOCAL_PATCH_REG_HEIGHT)
            if method_lalign == LALIGN_NORMAL:
                if method_galign == GALIGN_CV:
                    I_patch = I_patch.astype('float32')
                    I_patch[:,:] /= 255.0
                    IrefM_patch = IrefM_patch.astype('float32')
                    IrefM_patch[:,:] /= 255.0
                H2, I1_patch, err = imagesAlign(I_patch, IrefM_patch, fillval=1, 
                                                rszFac=rszFac, trfm_type='rigid', minArea=np.power(2, 18))
                I1_patch = np.round(I1_patch * 255.0).astype('uint8')
            elif method_lalign == LALIGN_CV:
                if method_galign == GALIGN_NORMAL:
                    I_patch = np.round(I_patch * 255.0).astype('uint8')
                    IrefM_patch = np.round(IrefM_patch * 255.0).astype('uint8')
                H2, I1_patch, err = global_align.align_cv(I1_patch, IrefM_patch, computeErr=True, 
                                                          rmBlkBorder=True, fullAffine=False,
                                                          doSmooth=True, smooth_sigma=12)

            targ = np.copy(I1_patch[bbOff[0]:bbOff[1], bbOff[2]:bbOff[3]])
            # 2.) Unwind transformation to get the global location of TARG
            rOut_tr=pttransform(I,np.linalg.inv(H1),np.array([bbExp[2],bbExp[0],1]))
            rOff_tr=pttransform(I_patch,np.linalg.inv(H2),np.array([bbOff[2],bbOff[0],1]))
            targLocGl=np.zeros(4)
            iLen = bbOff[1] - bbOff[0]
            jLen = bbOff[3] - bbOff[2]
            targLocGl[0]=round(rOut_tr[1]+rOff_tr[1])
            targLocGl[1]=round(rOut_tr[1]+rOff_tr[1]+iLen)
            targLocGl[2]=round(rOut_tr[0]+rOff_tr[0])
            targLocGl[3]=round(rOut_tr[0]+rOff_tr[0]+jLen)

            # weird bug in imsave where if the matrix is all ones, it saves as pure black
            result.append((bb[4],targ,map(int,tuple(targLocGl)),err))
    else:
        # parameter specified number of cells
        # for each cell, grab the targets that fall in the center
        #   compute super-region and pad
        vStep=math.ceil(Iref.shape[0]/vCells);
        hStep=math.ceil(Iref.shape[1]/hCells);
        H1_inv = np.linalg.inv(H1)
        for i in range(vCells):
            for j in range(hCells):
                i1=i*vStep; j1=j*hStep;
                i2=(i+1)*vStep-1; i2=min(i2,I1.shape[0]-1);
                j2=(j+1)*hStep-1; j2=min(j2,I1.shape[1]-1);
                # grab all targets within this range
                bbs1=bbsInCell(bbs,i1,i2,j1,j2)
                if bbs1.size == 0:
                    continue

                (bbOut,bbsOff)=sh.expandBbs(bbs1,I.shape[0],I.shape[1],pFac)

                Ic=sh.cropBb(I1,bbOut)
                IrefcNOMASK=sh.cropBb(Iref,bbOut)
                Irefc=sh.cropBb(IrefM,bbOut)
                rszFac=sh.resizeOrNot(Ic.shape,sh.LOCAL_PATCH_REG_HEIGHT)
                if method_lalign == LALIGN_NORMAL:
                    if method_galign == GALIGN_CV:
                        Ic = Ic.astype('float32') / 255.0
                        Irefc = Irefc.astype('float32') / 255.0
                    #Hc1, Ic1, err = imagesAlign(Ic,Irefc,fillval=1,rszFac=rszFac,trfm_type='rigid',minArea=np.power(2,16))
                    Hc1, Ic1, err = global_align.align_image(Ic, Irefc, crop=True, CROPX=0.05, CROPY=0.05, MINAREA=np.power(2, 16))
                    #if i == 3 and j == 3:
                    #    print "i,j=", i,j
                    #    misc.imsave("Ic_reg_{0}_{1}.png".format(i, j), Ic1+Irefc)
                    #    pdb.set_trace()
                    Ic1 = np.round(Ic1 * 255.0).astype('uint8')
                elif method_lalign == LALIGN_CV:
                    if method_galign == GALIGN_NORMAL:
                        Ic = np.round(Ic * 255.0).astype('uint8')
                        Irefc = np.round(Irefc * 255.0).astype('uint8')
                    Hc1, Ic1, err = global_align.align_cv(Ic, Irefc, computeErr=True,
                                                          rmBlkBorder=True, fullAffine=False,
                                                          doSmooth=True, smooth_sigma=12)
                    Hc1_sq = np.eye(3, dtype=H1.dtype)
                    Hc1_sq[:2, :] = Hc1
                    Hc1 = Hc1_sq
                Hc1_inv = np.linalg.inv(Hc1)
                for k in range(bbsOff.shape[0]):
                    bbOff1=bbsOff[k,:]
                    iLen=bbOff1[1]-bbOff1[0]
                    jLen=bbOff1[3]-bbOff1[2]
                    #targ=np.copy(sh.cropBb(Ic1,bbOff1))
                    targ = sh.cropBb(Ic1, bbOff1)
                    # unwind the transformations to get the global location of the target
                    rOut_tr=pttransform(I, H1_inv, np.array([bbOut[2],bbOut[0],1]))
                    rOff_tr=pttransform(Ic, Hc1_inv, np.array([bbOff1[2],bbOff1[0],1]))
                    targLocGl = (int(round(rOut_tr[1]+rOff_tr[1])),
                                 int(round(rOut_tr[1]+rOff_tr[1]+iLen)),
                                 int(round(rOut_tr[0]+rOff_tr[0])),
                                 int(round(rOut_tr[0]+rOff_tr[0]+jLen)))
                    # weird bug in imsave where if the matrix is all ones, it saves as pure black
                    result.append((bbs1[k,4],targ, targLocGl,err))

    if(verbose):
        print 'total extract time = ',time.clock()-t0,'(s)'
    return result

def writeMAP(imgs, targetDir, targetDiffDir, imageMetaDir, balId,
             balP, tplP, flipped, page,
             voted_rootdir, projdir, result_queue):
    """
    Note: All input target images must have dtype='uint8' and in range [0,255].
    """
    imgname = os.path.splitext(os.path.split(balP)[1])[0]

    relpath_root = os.path.relpath(os.path.abspath(os.path.split(balP)[0]), os.path.abspath(voted_rootdir))
    relpath_root = os.path.normpath(relpath_root)
    targetout_rootdir = os.path.normpath(os.path.join(targetDir, relpath_root, imgname, "page{0}".format(page)))
    #targetmetaout_rootdir = os.path.normpath(os.path.join(targetMetaDir, relpath_root, imgname, "page{0}".format(page)))
    targetdiffout_rootdir = os.path.normpath(os.path.join(targetDiffDir, relpath_root, imgname, "page{0}".format(page)))
    imgmetaout_rootdir = os.path.normpath(os.path.join(imageMetaDir, relpath_root, imgname, "page{0}".format(page)))
    
    #try: os.makedirs(targetmetaout_rootdir)
    #except: pass
    try: os.makedirs(targetdiffout_rootdir)
    except: pass
    try: os.makedirs(imgmetaout_rootdir)
    except: pass

    curid = str(id(mp.current_process()))
    radix_sort_dir = os.path.join(os.path.abspath(projdir), "extracted_radix/"+curid)
    #print radix_sort_dir
    try: os.makedirs(radix_sort_dir)
    except: pass

    avg_intensities = [] # [(str targetname, float avg_intensity), ...]

    # 1.) First, save target patches, target diff data, and target meta
    #     data to disk, and reconstruct directory structure.
    targets = [] # [str _i, ...]
    bboxes = []

    def get_target_roi():
        try:
            file_targetroi = open(os.path.join(projdir, 'target_roi'), 'r')
            line = file_targetroi.readline().strip()
            x1, y1, x2, y2 = map(int, line.split(","))
            return x1, y1, x2, y2
        except:
            return None

    t_roi = get_target_roi()

    for uid,img,bbox,Idiff in imgs:
        targetoutname = str(balId)+"\0"+str(page)+"\0"+str(int(uid))
        targets.append((balId, page, int(uid)))
        if not HACK_SANTACRUZ:
            if not t_roi:
                tpatch = img
            else:
                x1, y1, x2, y2 = t_roi
                tpatch = img[y1:y2, x1:x2]
            avg_intensity = np.mean(tpatch)
        else:
            # SantaCruz - specific HACK
            _INTEREST = img[:, 15:img.shape[1]-20]
            avg_intensity = np.sum(_INTEREST) / float(_INTEREST.shape[0]*_INTEREST.shape[1])
        avg_intensities.append((targetoutname, avg_intensity))
        diffoutname = imgname + "." + str(int(uid)) + ".npy"
        np.save(pathjoin(targetdiffout_rootdir, diffoutname), Idiff)

        #metaoutname = imgname + '.' + str(int(uid))
        #metafile = pathjoin(targetmetaout_rootdir, metaoutname)
        #pickle.dump({'bbox':bbox}, open(metafile, "w"))
        bboxes.append(bbox)

        placefile = os.path.join(radix_sort_dir, "%02x"%int(avg_intensity))
        data = array.array("B", np.floor(img.flatten()).astype('uint8')).tostring()
        if os.path.exists(placefile):
            open(placefile, "a").write(data)
            open(placefile+".index", "a").write(targetoutname+"\n")
        else:
            open(placefile, "w").write(data)
            open(placefile+".index", "w").write(targetoutname+"\n")
    
    # 2.) Finally, save image meta-data to disk.
    imgmeta_outpath = os.path.join(imgmetaout_rootdir, "{0}_meta.p".format(imgname))
    toWrite={"flipped": flipped, 
             "targets":targets, 
             "target_bboxes":bboxes,
             "ballot": balP, 
             "template": tplP}
    # store the grouping and local alignment error with the ballot metadata.
    # use this for quarintine purposes.
    #bbox_errs=[];
    #for uid,img,bbox,err in imgs:
    #    bbox_errs.append(err);
    #toWrite["bbox_errs"]=str(bbox_errs);
    pickle.dump(toWrite, open(imgmeta_outpath, "w"))
    result_queue.put([avg_intensities, balP, page, targetout_rootdir, 
                      targetdiffout_rootdir, imgmeta_outpath])

def debugWorker(job):
    (Iref, bbs, fIn, destDir, extractedMeta, contestMeta, f1) = job
    
    I=sh.standardImread(fIn)
    # trim down or expand I to fit Iref
    I1=np.ones([Iref.shape[0],Iref.shape[1]],dtype='float32')
    h=min(Iref.shape[0],I.shape[0])-1; w=min(Iref.shape[1],I.shape[1])-1;
    I1[1:h,1:w]=I[1:h,1:w]

    # check if ballot is flipped
    res=checkBallotFlipped(I1,Iref)
    Ichk=res[1]; flipped=res[0]
    # extract target and write result
    return (Ichk,extractTargets(Ichk,Iref,bbs))

def findOutliers(Errs,thr,N):

    sidx=np.argsort(Errs)
    sidx=sidx[::-1]

    qFlag=[]
    for i in range(len(sidx)):
        j = i+1
        found=False
        while ((j-i)<(N+1)) & (j < len(sidx)):

            dif=Errs[sidx[i]]-Errs[sidx[j]]
            if dif>thr:
                qFlag.append(sidx[i])
                found=True
                break
            else:
                j+=1

        if ~found:
            break
                
    return qFlag


def quarantineCheckMAP(jobs, targetDiffDir, quarantined_outP, img2bal, bal2targets, imageMetaDir=[] ):
    """
    Input:
        dict BAL2TARGETS: maps {int ballotid: {int page: [targetdir, targetmetadir, diffdir, imgmetapath]}}
    """
    # Algorithm.
    # Pick percentage p,e.g., .1%
    # Set D to range(x)
    # - Sort 
    # - from largest x, read in nearest neighbors
    # - if any neighbor is more than D distance away, flag outlier
    # - else: break

    print 'done. now computing quarantine info.'
    # identify outliers and quarantine if necessary

    print 'Done w/ hash.'
    if wx.App.IsMainLoopRunning():
        wx.CallAfter(Publisher().sendMessage, "signals.MyGauge.nextjob", len(jobs))

    # STEP 1: load in all error values
    ErrHash={}
    JobHash={}
    Errs=[];K=0
    
    for K in range(len(jobs)):
        # job := [tplImgs, tplPaths, tplFlips, bbsL_i, balL_i, balid, balL_flips, targetDiri, targetDiffDir_i, imageMetaDir_i, voteddir, projdir, queue, result_queue]
        job=jobs[K]
        balL=job[4]
        for side, balP in enumerate(balL):
            ballotid = img2bal[balP]
            try:
                _, diffdir, imgmetapath = bal2targets[ballotid][side]
            except:
                traceback.print_exc()
                pdb.set_trace()
            diffpaths = [pathjoin(diffdir, f) for f in os.listdir(diffdir)]
            if not diffpaths:
                # means this side had no targets - skip it
                continue
            if len(diffpaths) == 1:
                # this side only had one target. This ends up
                # crashing the following line:
                #     Errs=np.vstack((Errs,np.squeeze(M1)[sidx]))
                # skip it to avoid the crash. a side with
                # /only/ one target is strange - shouldn't ever happen
                print "Warning: the following ballot had only one voting \
target defined. This is probably a mistake in SelectTargets!\n\
    {0}".format(balP)
                continue

            # loop over jobs
            M1=[]; IDX1=np.empty(0);
            for f1 in diffpaths:
                # Recall: difname is {imgname}.{uid}.npy
                (f2,npext)=os.path.splitext(f1)
                (foo,idx)=os.path.splitext(f2)
                idx=eval(idx[1:])
                Idiff=np.load(f1)

                M1.append(Idiff)
                IDX1=np.append(IDX1,idx)
                
            # sort idx to straighten out order
            sidx=np.argsort(IDX1)

            # index into hash based on template
            if len(imageMetaDir)==0:
                k1='default'
            else:
                # TODO: MUST READ IN TEMPLATE SIDE FROM RESULT FILE                
                meta = pickle.load(open(imgmetapath, 'rb'))
                k1=str(meta['template'])
    
            if ErrHash.has_key(k1):
                Errs=ErrHash[k1]
                jList=JobHash[k1]
            else:
                Errs=np.zeros((0,len(sidx)))
                jList=[]
            Errs=np.vstack((Errs,np.squeeze(M1)[sidx]))
            jList.append(balP)
            ErrHash[k1]=Errs
            JobHash[k1]=jList
            K+=1
            if wx.App.IsMainLoopRunning():
                wx.CallAfter(Publisher().sendMessage, "signals.MyGauge.tick")

    print 'Done reading in errs.'

    qFiles=[]
    # perform outlier check for each template (key)
    for key in ErrHash.keys():
        qFlag=[]
        Errs=ErrHash[key]
        jList=JobHash[key]
        thr=(np.max(Errs,0)-np.min(Errs,0))/2
        
        #NP=max(round(len(jList)*.001),0)
        NP=max(round(len(jList)*.01),0)
        # compute D for each dimension
        # for each dimension
        #   sort
        #   for worst one, compare to nearest k
        #     if any are outside d, flag, and move to next point
        #     else: break to next dim
        for i in range(Errs.shape[1]):
            Errs1=Errs[:,i]
            qFlag+=findOutliers(Errs1,thr[i],NP)

        for i in range(len(qFlag)):
            #print qFlag
            #print jList
            #print i
            qFiles.append(jList[qFlag[i]])

    qFiles=list(set(qFiles))
    qBallotIds = list(set([img2bal[imP] for imP in qFiles]))
    #qBallotIds = [1, 3]  # TODO: TEST

    print "...Quarantined {0} ballots during TargetExtraction...".format(len(qBallotIds))
    pickle.dump(qBallotIds, open(quarantined_outP, 'wb'))

    return qBallotIds

def convertImagesWorkerMAP(job):
    # match to front-back
    # (list of template images, target bbs for each template, filepath for image,
    #  output for targets, output for quarantine info, output for extracted
    #(tplImgs, tplPaths, tpl_flips, bbsL, balL, targetDir, targetDiffDir, targetMetaDir, imageMetaDir, queue, method_galign, method_lalign) = job
    #print "START"
    try:
        (tplImgs, tplPaths, tpl_flips, bbsL, balL, balId, balL_flips, targetDir, targetDiffDir, imageMetaDir, voted_rootdir, projdir, queue, result_queue, method_galign, method_lalign) = job
        t0=time.clock();

        # load images
        balImL=[]
        for i, imP in enumerate(balL):
            if method_galign == GALIGN_NORMAL:
                balImg = sh.standardImread_v2(imP, flatten=True, dtype='float32', normalize=True)
            else:
                balImg = sh.standardImread_v2(imP, flatten=True, dtype='uint8', normalize=False)
            if balL_flips[i]:
                balImg = sh.fastFlip(balImg)
            balImL.append(balImg)

        # check if ballot is flipped
        t0=time.clock();

        for side, tplImg in enumerate(tplImgs):
            if tplImg == None:
                # This group didn't have its 'template' images pre-loaded
                if method_galign == GALIGN_NORMAL:
                    tplImg = sh.standardImread_v2(tplPaths[side], flatten=True, dtype='float32', normalize=True)
                else:
                    tplImg = sh.standardImread_v2(tplPaths[side], flatten=True, dtype='uint8', normalize=False)
                if tpl_flips[side]:
                    tplImg = sh.fastFlip(tplImg)
            tplImgPath = tplPaths[side]
            balImg = balImL[side]
            balP = balL[side]
            bbs = bbsL[side]
            flipped = balL_flips[side]
            writeMAP(extractTargetsRegions(balImg,tplImg,bbs,
                                           balP=balP,do_grid_opt=True,
                                           vCells=4,hCells=4, verbose=False,
                                           method_galign=method_galign,
                                           method_lalign=method_lalign), 
                     targetDir, targetDiffDir, 
                     imageMetaDir, balId, balP, tplImgPath,
                     flipped, side, voted_rootdir, projdir, result_queue)
        queue.put(True)
    except Exception as e:
        traceback.print_exc()
        queue.put(e.message)
    #print "DONE"

def convertImagesMasterMAP(targetDir, targetMetaDir, imageMetaDir, jobs, 
                           img2bal, stopped, queue, result_queue,
                           num_imgs2process,
                           verbose=False, nProc=None,
                           method_galign=GALIGN_NORMAL,
                           method_lalign=LALIGN_NORMAL):
    """ Called by both single and multi-page elections. Performs
    Target Extraction.
    Input:
        str targetDir: Directory to dump extracted target images to.
        str targetMetaDir: Directory to store target metadata into.
        str imageMetaDir: Directory to store metadata for each Ballot,
            such as ballotpath, path to each extracted target, assoc'd
            blank ballot, isflipped.
        list jobs: [[tmppaths_i, bbs_i, imgpaths_i, targetDir_i, targetDiffDir_i, imageMetaDir_i, queue], ...]
        stopped:
    """
    targetDiffDir=targetDir+'_diffs'

    print "...removing previous Target Extract results..."
    _t = time.time()
    if os.path.exists(targetDir): shutil.rmtree(targetDir)
    if os.path.exists(targetDiffDir): shutil.rmtree(targetDiffDir)
    if os.path.exists(targetMetaDir): shutil.rmtree(targetMetaDir)
    if os.path.exists(imageMetaDir): shutil.rmtree(imageMetaDir)
    dur = time.time() - _t
    print "...Finished removing previous Target Extract results ({0} s).".format(dur)

    create_dirs(targetDir)
    create_dirs(targetDiffDir)
    create_dirs(targetMetaDir)
    create_dirs(imageMetaDir)

    if nProc == None:
        nProc = sh.numProcs()
    #nProc = 1
    num_jobs = len(jobs)
    
    if nProc < 2:
        print 'using only 1 processes'
        # default behavior for non multiproc machines
        for job in jobs:
            if stopped():
                return False
            t0=time.clock();
            convertImagesWorkerMAP(job)
            print time.clock()-t0
    else:
        print 'using ', nProc, ' processes'
        pool=mp.Pool(processes=nProc)

        '''
        it = [False]
        def imdone(x):
            it[0] = True
            print "I AM DONE NOW!"
        '''
        if wx.App.IsMainLoopRunning():
            wx.CallAfter(Publisher().sendMessage, "signals.MyGauge.nextjob", num_jobs)
        print "GOING UP TO", num_jobs
        #pool.map_async(convertImagesWorkerMAP,jobs,callback=lambda x: imdone(it))
        pool.map_async(convertImagesWorkerMAP, jobs)
        cnt = 0
        while cnt < len(jobs):
            val = queue.get(block=True)
            if val == True:
                if wx.App.IsMainLoopRunning():
                    wx.CallAfter(Publisher().sendMessage, "signals.MyGauge.tick")
                cnt += 1
            elif type(val) in (str, unicode):
                # Something went wrong!
                print "    WARNING: detected a failed extract job {0}.".format(cnt)
                cnt += 1
        pool.close()
        pool.join()

    print "    (Finished processing targetextract jobs)"

    cnt = 0
    avg_intensities = [] # [(path, float avg_intensity), ...]
    bal2targets = {} # maps {int ballotid: {int page: [targetsdir, targetmetadir, diffmetadir, imgmetadir]}}

    while cnt < num_imgs2process:
        (avg_intensities_cur, balP, page, target_rootdir,
         targetdiff_rootdir, imgmeta_rootdir) = result_queue.get(block=True)
        avg_intensities.extend(avg_intensities_cur)
        ballotid = img2bal[balP]
        #print "...finished ballotid {0}".format(ballotid)
        bal2targets.setdefault(ballotid, {})[page] = (target_rootdir,
                                                      targetdiff_rootdir, imgmeta_rootdir)
        cnt += 1
    print 'done.'
    return avg_intensities, bal2targets

def fix_ballot_order(balL, proj=None, bal2page=None):
    """ Using ballot_to_page, correct the image ordering (i.e. 'side0',
    'side1', ...
    Input:
        lst balL: [imgpath_i, ...]
        obj proj
    Output:
        [side0_path, side1_path, ...]
    """
    assert issubclass(type(balL), list)
    if bal2page == None:
        bal2page = pickle.load(open(os.path.join(proj.projdir_path,
                                                 proj.ballot_to_page),
                               'rb'))
    out = [None]*len(balL)
    for imgpath in balL:
        if imgpath not in bal2page:
            print "Uh oh, imgpath not in bal2page."
            pdb.set_trace()
        assert imgpath in bal2page
        side = bal2page[imgpath]
        assert issubclass(type(side), int)
        out[side] = imgpath
    assert None not in out
    return out

def hack_stopped():
    return False

def extract_targets(group_to_ballots, b2imgs, img2b, img2page, img2flip, target_locs_map,
                    group_exmpls, bad_ballotids,
                    targetDir, targetMetaDir, imageMetaDir,
                    targetextract_quarantined, voted_rootdir, projdir, stopped=None,
                    nProc=None,
                    method_galign=GALIGN_NORMAL,
                    method_lalign=LALIGN_NORMAL):
    """ Target Extraction routine, for the new blankballot-less pipeline.
    Input:
        dict GROUP_TO_BALLOTS: maps {groupID: [int ballotID_i, ...]}
        dict B2IMGS: maps {int ballotID: (imgpath_i, ...)}
        dict IMG2B: maps {imgpath: int ballotID}
        dict IMG2PAGE: maps {imgpath: int page}
        dict IMG2FLIP: maps {imgpath: bool isflip}
        dict TARGET_LOCS_MAP: maps {int groupID: {int page: [[cbox_i, tbox_i, ...], ...]}},
            where each box_i := [x1, y1, w, h, id, contest_id]
        dict GROUP_EXMPLS: maps {int groupID: [int ballotID_i, ...]}
        list BAD_BALLOTIDS: BallotIDs that were either previous quarantined or discarded.
        str TARGETDIR: Dir to store extracted target patches
        str TARGETMETADIR: Dir to store metadata for each target
        str IMAGEMETADIR: Dir to store metadata for each ballot
        str TARGETEXTRACT_QUARANTINED: 
        fn STOPPED: Intended to be used as a way to cancel the extraction,
            i.e. returns True if we should.
        int NPROC: Number of processors to use (if None, then # cores on machine)
        int METHOD_GALIGN: The global alignment method to use. One of:
            GALIGN_NORMAL, GALIGN_CV
        int METHOD_LALIGN: The local alignmeng method to use. One of:
            LALIGN_NORMAL, LALIGN_CV, LALIGN_NONE
    Output:
        bool WORKED. True if everything ran correctly, False o.w.
    """
    def get_bbs(groupID, target_locs_map):
        bbs_sides = []
        boxes_sides = target_locs_map[groupID]
        for side, contests in sorted(boxes_sides.iteritems(), key=lambda t: t[0]):
            bbs = np.empty((0, 5))
            for contest in contests:
                cbox, tboxes = contest[0], contest[1:]
                for tbox in tboxes:
                    x1 = tbox[0]
                    y1 = tbox[1]
                    x2 = tbox[0] + tbox[2]
                    y2 = tbox[1] + tbox[3]
                    if HACK_SANTACRUZ:
                        x1 += 33
                        x2 -= 23

                    id = tbox[4]
                    bb = np.array([y1, y2, x1, x2, id])
                    bbs = np.vstack((bbs, bb))
            bbs_sides.append(bbs)
        return bbs_sides

    if stopped == None:
        stopped = lambda : False
    targetDiffDir = targetDir + '_diffs'
    # JOBS: [[blankpaths_i, bbs_i, votedpaths_i, targetDir, targetDiffDir, targetMetaDir, imgMetaDir, queue], ...]
    jobs = []
    # 1.) Create jobs
    manager = mp.Manager()
    queue = manager.Queue()
    result_queue = manager.Queue()
    imgcount = 0
    print "Creating blank ballots; go up to", len(group_to_ballots)
    _galignnames = {GALIGN_NORMAL: "NORMAL", GALIGN_CV: "CV"}
    _lalignnames = {LALIGN_NORMAL: "NORMAL", LALIGN_CV: "CV", LALIGN_NONE: "NONE"}
    print "(Info) METHOD_GALIGN={0} METHOD_LALIGN={1}".format(_galignnames[method_galign], _lalignnames[method_lalign])
    MAX_SIZE = 950 * (1e6) # In Bytes, e.g. 950 MB. Limit memory usage of template pre-loading
    cur_size = 0
    if os.path.exists(os.path.join(projdir,'group_to_Iref.p')):
        group_to_Iref = pickle.load(open(os.path.join(projdir,'group_to_Iref.p'),'rb'))
    else:
        group_to_Iref = None

    if os.path.exists(os.path.join(projdir, 'quarantinedgroups_seltargets.p')):
        # groups that were quarantined ('flagged') during SelectTargets.
        groups_quar = pickle.load(open(os.path.join(projdir, 'quarantinedgroups_seltargets.p')))
    else:
        groups_quar = set()

    for i,(groupID, ballotIDs) in enumerate(sorted(group_to_ballots.iteritems(), key=lambda t: -len(t[1]))):
        if groupID in groups_quar:
            continue
        bbs = get_bbs(groupID, target_locs_map)
        # 1.a.) Choose reference images for alignment purposes
        if group_to_Iref and groupID in group_to_Iref.keys():
            idx = group_to_Iref[groupID]
        else:
            idx = 0 # default case select the first ballot in the group
        blankpaths_ordered  = []

        exmpl_id = group_exmpls[groupID][idx]
        blankpaths = b2imgs[exmpl_id]
        blankpaths_ordered = sorted(blankpaths, key=lambda imP: img2page[imP])
        blankpaths_flips = [img2flip[blank_imP] for blank_imP in blankpaths_ordered]
        
        blankimgs = []
        for i, blankpath in enumerate(blankpaths_ordered):
            isflip = blankpaths_flips[i]
            if cur_size >= MAX_SIZE:
                blankimgs.append(None)
            else:
                if method_galign == GALIGN_NORMAL:
                    Iblank = sh.standardImread_v2(blankpath, flatten=True, dtype='float32', normalize=True)
                else:
                    Iblank = sh.standardImread_v2(blankpath, flatten=True, dtype='uint8', normalize=False)
                if isflip:
                    Iblank = sh.fastFlip(Iblank)
                cur_size += Iblank.nbytes
                blankimgs.append(Iblank)
        for ballotid in ballotIDs:
            if ballotid in bad_ballotids:
                continue
            imgpaths = b2imgs[ballotid]
            imgpaths_ordered = sorted(imgpaths, key=lambda imP: img2page[imP])
            imgpaths_flips = [img2flip[imP] for imP in imgpaths_ordered]
            job = [blankimgs, blankpaths_ordered, blankpaths_flips, bbs, imgpaths_ordered,
                   ballotid, imgpaths_flips, targetDir, targetDiffDir, imageMetaDir, 
                   voted_rootdir, projdir, queue, result_queue, method_galign, method_lalign]
            jobs.append(job)
            imgcount += len(imgpaths_ordered)
    avg_intensities, bal2targets = convertImagesMasterMAP(targetDir, targetMetaDir, imageMetaDir, jobs, img2b, stopped, queue, result_queue, imgcount, nProc=nProc, method_galign=method_galign,method_lalign=method_lalign)
    if avg_intensities:
        # Quarantine any ballots with large error
        t = time.time()
        print "...Starting quarantineCheckMAP..."
        qballotids = quarantineCheckMAP(jobs,targetDiffDir,targetextract_quarantined,img2b, bal2targets, imageMetaDir=imageMetaDir)

        # Remove all quarantined ballots from AVG_INTENSITIES, BAL2TARGETS
        def is_quarantined(targetpath, voteddir, extractdir, qballotids, img2b):
            votedimgpath = target_to_image(targetpath, b2imgs)
            ballotid = img2b[votedimgpath]
            #if ballotid in qballotids:
            #    print "    CAUGHT QBALLOTID", ballotid
            return ballotid in qballotids
            
        avg_intensities = [tup for tup in avg_intensities if not is_quarantined(tup, voted_rootdir, targetDir, qballotids, img2b)]
        for qballotid in qballotids:
            bal2targets.pop(qballotid)
        dur = time.time() - t
        print "...Finished quarantineCheckMAP ({0} s).".format(dur)
    return avg_intensities, bal2targets

def target_to_image(target, b2imgs):
    bid, side, _= target[0].split("\0")
    return b2imgs[int(bid)][int(side)]
