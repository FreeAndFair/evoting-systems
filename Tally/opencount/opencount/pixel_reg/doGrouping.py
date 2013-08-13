from os.path import join as pathjoin
from scipy import misc
import shared as sh
from imagesAlign import *
import cv
import traceback, os, shutil, time
import multiprocessing as mp
import wx
from wx.lib.pubsub import Publisher
try:
    import cPickle as pickle
except ImportError:
    import pickle
from util import encodepath, GaugeID

JOBID_GROUPING_IMGBASED = GaugeID("GROUPING_IMGBASED")

def doWrite(finalOrder, Ip, err, attrName, patchDir, metaDir, origfullpath):
    fullpath = encodepath(origfullpath)

    # - patchDir: write out Ip into patchDir
    Ip[np.isnan(Ip)]=1
    to = os.path.join(patchDir, fullpath + '.png')
    sh.imsave(to,Ip)

    # - metaDir:
    # loop over finalOrder and compile array of group IDs and flip/nonflip
    attrOrder=[]; flipOrder=[];
    for pt in finalOrder:
        # pt[2] := (str temppath, str attrval)
        attrOrder.append(pt[2][1])
        flipOrder.append(pt[3])
    
    to = os.path.join(metaDir, fullpath)
    toWrite={"attrOrder": attrOrder, "flipOrder":flipOrder,"err":err}
    file = open(to, "wb")
    pickle.dump(toWrite, file)
    file.close()

def doWriteMAP(finalOrder, Ip, err, attrtype, patchDir, ballotid, exemplar_idx):
    """
    Input:
        list FINALORDER: [(nparray imgpatch, nparray attrpatch, attrval, int imgorder, bool isflip), ...]
        ...
        int exemplar_idx: Which exemplar attrpatch did this match to?
    Output:
        list OUT. [int ballotid, str attrtype, dict outdict].
    """
    # TODO: For now, just use the int ballotID itself, in a flat
    # dirstruct manner.
    #fullpath = encodepath(balKey)
    fullpath = str(ballotid)

    # - patchDir: write out Ip into patchDir
    Ip[np.isnan(Ip)]=1
    to = os.path.join(patchDir, fullpath + '.png')
    misc.imsave(to,Ip)

    # - metaDir:
    # loop over finalOrder and compile array of group IDs
    attrOrder=[]
    for pt in finalOrder:
        attrOrder.append(pt[2])
    
    #to = os.path.join(metaDir, fullpath)
    #toWrite={"attrOrder": attrOrder, "flipOrder":flipOrder,"err":err,"imageOrder":imageOrder,
    #         "exemplar_idx": exemplar_idx}
    outdict = {'attrOrder': attrOrder, 'err': err, 'exemplar_idx': exemplar_idx, 'patchpath': to}
    out = [ballotid, attrtype, outdict]
    #file = open(to, "wb")
    #pickle.dump(toWrite, file)
    #file.close()
    return out

def evalPatchSimilarity(I,patch, debug=False):
    # perform template matching and return the best match in expanded region
    I_in = np.copy(I)
    patch_in = np.copy(patch)

    if debug == True:
        print "...stepping into evalPatchSimilarity."
        pdb.set_trace()

    I=sh.prepOpenCV(I)
    patch=sh.prepOpenCV(patch)
    # See pixel_reg/eric_np2cv/demo.py for why I scale by 255.0 when 
    # converting NP -> OpenCV.
    patchCv=cv.fromarray(np.copy(patch) * 255.0)
    ICv=cv.fromarray(np.copy(I) * 255.0)
    #patchCv=cv.fromarray(np.copy(patch))  
    #ICv=cv.fromarray(np.copy(I))
    
    # call template match
    outCv=cv.CreateMat(I.shape[0]-patch.shape[0]+1,I.shape[1]-patch.shape[1]+1,patchCv.type)
    cv.MatchTemplate(ICv,patchCv,outCv,cv.CV_TM_CCOEFF_NORMED)
    Iout=np.asarray(outCv) / 255.0
    #Iout=np.asarray(outCv)
    Iout[Iout==1.0]=0;
    YX=np.unravel_index(Iout.argmax(),Iout.shape)

    # local alignment: expand a little, then local align
    i1=YX[0]; i2=YX[0]+patch.shape[0]
    j1=YX[1]; j2=YX[1]+patch.shape[1]
    I1c=I[i1:i2,j1:j2]
    IO=imagesAlign(I1c,patch,trfm_type='rigid', minArea=np.power(2, 20))

    Ireg=IO[1]
    #Ireg = np.nan_to_num(Ireg)
    # TODO: Ireg is frequently just a competely-black image (due to
    # presence of Nan's?). By inserting the line:
    #     Ireg = np.nan_to_num(Ireg)
    # This stopped an apparent bug in Marin, where various attribute
    # patches would erroneously be matched to the wrong side of the
    # ballot.

    # C := num pixels to discard around border. This used to be C=5,
    #      but this caused issues if one of the 'patch' dimensions was
    #      <= 10, causing an ill-formed image patch.
    AMT = 0.2
    C_i = int(round(Ireg.shape[0] * AMT))
    C_j = int(round(Ireg.shape[1] * AMT))
    D_i = int(round(patch.shape[0] * AMT))
    D_j = int(round(patch.shape[1] * AMT))
    bb_1 = [C_i, 
            min(Ireg.shape[0]-1, Ireg.shape[0]-C_i),
            C_j, 
            min(Ireg.shape[1]-1, Ireg.shape[1]-C_j)]
    bb_2 = [D_i,
            min(patch.shape[0]-1, patch.shape[0]-D_i),
            D_j,
            min(patch.shape[1]-1, patch.shape[1]-D_j)]
    if bb_1[0] >= bb_1[1]:
        bb_1[0] = 0
    if bb_1[1] <= 2:
        bb_1[1] = Ireg.shape[0]-1
    if bb_1[2] >= bb_1[3]:
        bb_1[2] = 0
    if bb_1[3] <= 2:
        bb_1[3] = Ireg.shape[1]-1

    if bb_2[0] >= bb_2[1]:
        bb_2[0] = 0
    if bb_2[1] <= 2:
        bb_2[1] = patch.shape[0]-1
    if bb_2[2] >= bb_2[3]:
        bb_2[2] = 0
    if bb_2[3] <= 2:
        bb_2[3] = patch.shape[1]-1
    #Ireg1=Ireg[C:Ireg.shape[0]-C,C:Ireg.shape[1]-C]
    #patch1=patch[C:patch.shape[0]-C,C:patch.shape[1]-C]
    Ireg1 = Ireg[bb_1[0]:bb_1[1], bb_1[2]:bb_1[3]]
    patch1 = patch[bb_2[0]:bb_2[1], bb_2[2]:bb_2[3]]

    if 0 in Ireg1.shape or 0 in patch1.shape:
        print "==== Uhoh, a crash is about to happen."
        print "Ireg.shape: {0}  patch.shape: {1}".format(Ireg.shape, patch.shape)
        print "Ireg1.shape: {0}  patch1.shape: {1}".format(Ireg1.shape, patch1.shape)
        print "bb_1:", bb_1
        print "bb_2:", bb_2
        misc.imsave("_evalpatchsim_ireg.png", Ireg)
        misc.imsave("_evalpatchsim_patch.png", patch)
        misc.imsave("_evalpatchsim_I1c.png", I1c)
        misc.imsave("_evalpatchsim_I.png", I)

    err = sh.variableDiffThr(Ireg1,patch1)
    diff=np.abs(Ireg1-patch1);
    # #estimate threshold for comparison: 

    return (-err,YX,diff)
    
def evalPatchSimilarity2(I,patch, debug=False):
    # perform template matching and return the best match in expanded region
    I_in = np.copy(I)
    patch_in = np.copy(patch)

    I=sh.prepOpenCV(I)
    patch=sh.prepOpenCV(patch)
    # See pixel_reg/eric_np2cv/demo.py for why I scale by 255.0 when 
    # converting NP -> OpenCV.
    patchCv=cv.fromarray(np.copy(patch) * 255.0)
    ICv=cv.fromarray(np.copy(I) * 255.0)
    #cv.SaveImage("_patchCv.png", patchCv)
    #cv.SaveImage("_ICv.png", ICv)
    #patchCv = tempmatch.smooth_mat(patchCv, 5, 5, bordertype='const', val=255)
    #ICv = tempmatch.smooth_mat(ICv, 5, 5, bordertype='const', val=255)
    #cv.SaveImage("_patchCv_smooth.png", patchCv)
    #cv.SaveImage("_ICv_smooth.png", ICv)
    #pdb.set_trace()
    # call template match
    outCv=cv.CreateMat(I.shape[0]-patch.shape[0]+1,
                       I.shape[1]-patch.shape[1]+1,patchCv.type)
    cv.MatchTemplate(ICv,patchCv,outCv,cv.CV_TM_CCOEFF_NORMED)
    #Iout=np.asarray(outCv) / 255.0
    Iout = np.asarray(outCv)
    YX=np.unravel_index(Iout.argmax(),Iout.shape)

    # take result and expand in each dimension by pixPad
    i1=YX[0]; i2=YX[0]+patch.shape[0]
    j1=YX[1]; j2=YX[1]+patch.shape[1]

    # [new] patch pad 25%
    # if the result has any nans then we'll call that bad, 
    # undo the transformation and compute error wrt original 
    # inputs.

    pixPad = round(.25 * min(patch.shape));
    patchPad = np.empty((patch.shape[0]+2*pixPad,
                         patch.shape[1]+2*pixPad), dtype='float32')
    patchPad[:] = np.nan
    patchPad[pixPad:patch.shape[0]+pixPad,
             pixPad:patch.shape[1]+pixPad] = patch

    # check how much we need to pad in each dimension
    # if any values are positive, that means we need to pad
    # the difference
    i1pad = i1 - pixPad;
    i1exp = max(0,-i1pad);
    i1pad = (i1 - pixPad) + i1exp;

    i2pad = i2 + pixPad;
    i2exp = max(0,i2pad-I.shape[0]);
    i2pad = (i2 + pixPad) - i2exp;

    j1pad = j1 - pixPad;
    j1exp = max(0,-j1pad);
    j1pad = (j1 - pixPad) + j1exp;

    j2pad = j2 + pixPad;
    j2exp = max(0,j2pad-I.shape[1]);
    j2pad = (j2 + pixPad) - j2exp;

    # crop out padded patch
    I1c=I[i1pad:i2pad,j1pad:j2pad]

    # check for padding
    if (i1exp+i2exp+j1exp+j2exp) > 0:
        I1c = sh.padWithBorderHandling(I1c,i1exp,i2exp,j1exp,j2exp)

    # expand if necessary
    #hCells = max(int(round(I1c.shape[1] / 200)), 1)
    #vCells = max(int(round(I1c.shape[0] / 200)), 1)
    hCells, vCells = 1, 1
    
    IO=imagesAlign(I1c,patchPad,trfm_type='rigid',hCells=hCells, vCells=vCells, minArea=np.power(2, 15))
    if debug:
        pdb.set_trace()
    Ireg=IO[1]
    Ireg = Ireg[pixPad:patch.shape[0]+pixPad,
                pixPad:patch.shape[1]+pixPad]

    if np.sum(np.isnan(Ireg)) > 0:
        # if there are nan values [brought in from the border]
        # then that means the alignment result was pretty extreme
        err = np.inf
        diff = patch
    else:
        err = sh.variableDiffThr(Ireg, patch)
        diff = np.abs(Ireg-patch);

    return (-err,YX,diff)

def dist2patches(patchTuples,scale,debug=False):
    """
    Input:
        list patchTuples: EITHER (!) of the form:
              ((imgpatch_i, attrpatch_i, str attval_i, isflip_i), ...)
            or
              ((imgpatch_i, [attrpatch_i, ...], str attrval_i, int page_i, isflip_i), ...)
            I'm not entirely sure when it's a 4-tuple or a 5-tuple...but beware.
        float scale: Current scale factor.
    Output:
        (scores, locs, exemplar_idxs)
    """
    # patchTuples ((K img super regions),(K template patches))
    # for each pair, compute avg distance at scale sc
    scores=np.zeros(len(patchTuples))
    idx=0;
    locs=[]
    exemplar_idxs = []  # Keeps track of which exemplar patch was the best for a given voted ballot

    for idx in range(len(patchTuples)):
        # pt is either 4-tuple:
        #     ((imgpatch_i,[attrpatch_i, ...],,attrval_i,isflip_i), ...)
        # or a 5-tuple:
        #     ((imgpatch_i,[attrpatch_i, ...],attrval_i,page_i,isflip_i), ...)
        pt=patchTuples[idx]
        imgpatch = pt[0]
        attrpatches = pt[1]
        attrval = pt[2]
        flag = False
        # A fix for a very bizarre openCv bug follows..... [check pixel_reg/opencv_bug_repo.py]
        I=np.round(sh.fastResize(imgpatch,scale)*255.)/255.
        # opencv appears to not like pure 1.0 and 0.0 values.
        #I[I==1.0]=.999; I[I==0.0]=.001
        #patchScale = sh.resizeOrNot(attrpatch.shape, int(round(max(attrpatch.shape)*scale)))
        bestscore = None
        bestloc = None
        best_idx_ex = None # Index of the best exemplar
        # Get the best score, over all possible exemplars (this is to
        # account for background variation). 
        for idx_ex, attrpatch in enumerate(attrpatches):
            patch=np.round(sh.fastResize(attrpatch,scale)*255.)/255.
            #patch[patch==1.0]=.999; patch[patch==0.0]=.001
            try:
                res=evalPatchSimilarity2(I,patch, debug=flag)
            except Exception as e:
                traceback.print_exc()
                print "CRASHED AT IDX:", idx
                print "    Scale was: {0}".format(scale)
                print "    I.shape: {0} patch.shape: {1}".format(I.shape, patch.shape)
                print "    imgpatch: {0} attrpatch: {1}".format(imgpatch.shape, attrpatch.shape)
                pdb.set_trace()
                raise e
            # TODO: Do I want to maximize, or minimize 'score'?
            score = res[0] # I'm pretty sure we want to maximize.
            score = res[0] / (patch.shape[0]*patch.shape[1])
            if bestscore == None or score > bestscore:
                bestscore = score
                best_idx_ex = idx_ex
                bestloc = (res[1][0]/scale,res[1][1]/scale)
            #scores[idx]=res[0]
            #locs.append((res[1][0]/scale,res[1][1]/scale))
        scores[idx] = bestscore
        locs.append(bestloc)
        exemplar_idxs.append(best_idx_ex)
    return (scores,locs, exemplar_idxs)

# input: image, patch images, super-region
# output: tuples of cropped image, patch image, template index, and flipped bit
#    ((I_i, attrexemplarpatch_i, str attrval, isflip_i), ...)
def createPatchTuples(I,attr2pat,R,flip=False):
    """
    Only used in templateSSWorker. Note: This is quite different from 
    createPatchTuplesMAP, despite the very similar name.
    Input:
        nparray I:
        dict ATTR2PAT: maps {str attrval: [(str imgpath, nparray patch_i), ...]}
        tuple R: SuperRegion.
    Output:
        tuple PATCHTUPLES. [[I_i, [exmpl_patch_i, ...], str attrval, bool isflip_i], ...]
    """
    pFac=1;
    if flip:
        I = sh.fastFlip(I)

    (rOut,rOff)=sh.expand(R[0],R[1],R[2],R[3],I.shape[0],I.shape[1],pFac)
    I1=I[rOut[0]:rOut[1],rOut[2]:rOut[3]]

    patchTuples=[];
    for attrval, exmpl_pairs in attr2pat.iteritems():
        patches = [t[1] for t in exmpl_pairs]
        patchTuples.append((I1,patches,attrval,flip))
    return patchTuples

def createPatchTuplesMAP(balL,attr2pat,R,flip=False):
    """
    Sort of creates 'tasks' for groupImagesWorkerMAP, where each task
    is a tuple of the form:
        (imgpatch_i, [attrpatch_i, ...], attrval_i, side_i, isflip_i)
    And you create one task for each side of a voted ballot (i.e. one
    for side0, another for side1, ...), to figure out the imgorder.
    Note that there can be multiple exemplar attrpatches.
    Input:
        tuple balL: (sidepath_i, ...)
        dict attr2pat: maps {str attrval: [(str imgpath, obj imgpatch_i), ...]}
        tuple R: (y1, y2, x1, x2). A 'super' region.
    Output:
        ((obj imgpatch_i, [obj attrpatch_i0, ...], str attrval_i, int side_i, int isflip_i), ...)
    """
    pFac=1;
    patchTuples=[];

    for idx in range(len(balL)):
        balP=balL[idx]
        I=sh.standardImread(balP,flatten=True)
        if flip:
            I = sh.fastFlip(I)
        (rOut,rOff)=sh.expand(R[0],R[1],R[2],R[3],I.shape[0],I.shape[1],pFac)
        I1=I[rOut[0]:rOut[1],rOut[2]:rOut[3]]
        for attrval, exemplar_pairs in attr2pat.iteritems():
            exmpl_patches = [t[1] for t in exemplar_pairs]
            patchTuples.append((I1, exmpl_patches, attrval, idx, flip))
    return patchTuples

def templateSSWorker(job):
    # dict attr2pat: maps {str attrval: [[str imgpath_i, obj patch_i], ...]}
    (attr2pat, attrval, superRegion, sStep, img2flip) = job
    
    attr2pat1=attr2pat.copy()
    # TODO: Arbitrarily chooses a patch_i
    (imgpath, patch) = attr2pat1[attrval][0]
    isflip = img2flip[imgpath]
    I=sh.standardImread(imgpath,flatten=True)
    
    superRegionNp=np.array(superRegion)
    patchTuples=createPatchTuples(I,attr2pat1,superRegionNp,flip=isflip)

    sc0=sh.resizeOrNot(patch.shape,sh.MAX_PRECINCT_PATCH_DIM)
    minSc=sh.resizeOrNot(patch.shape,sh.MIN_PRECINCT_PATCH_DIM)
    (scores0,locs,exemplar_idxs)=dist2patches(patchTuples,sc0)

    sidx=np.argsort(scores0)
    sidx=sidx[::-1]
    trackIdx=sidx[0]

    # sc1 is the 'scale' that we're currently working with.
    sc1=sc0-sStep  # Starting scale.

    while sc1>minSc:
        try:
            (scores,locs, exemplar_idxs)=dist2patches(patchTuples,sc1)
        except Exception as e:
            d = {'patchTuples': patchTuples, 'sc1': sc1}
            path = '_errdict_0'
            '''
            while os.path.exists(path):
                new_i = int(path.split("_")[-1]) + 1
                path = '_errdict_{0}'.format(str(new_i))
            print '...outputting debug info to:', path
            pickle.dump(d, open(path, 'wb'))
            '''
            print "Exiting."
            exit(1)

        sidx=np.argsort(scores)
        sidx=sidx[::-1]
        mid=np.ceil(len(sidx)/2.0)
        dumpIdx=sidx[mid:len(sidx)]
        if sum(0+(dumpIdx==trackIdx))>0:
            break
        else:
            # decrease the scale
            sc1=sc1-sStep

    # write scale to file
    #toWrite={"scale": min(sc1+sStep,sc0)}
    #file = open(fOut, "wb")
    #pickle.dump(toWrite, file)
    #file.close()
    templateSSWorker.queue.put(min(sc1+sStep, sc0))

def groupImagesWorkerMAP(job):
    try:
        #(ballotid, imgpaths, attrName, bb, attrinfo, attr2pat,scale) = job
        # Note: In blankballot-less pipeline, IMGPATHS is always a list of
        # one element - the imgpath that is the correct side for ATTRTYPE.
        (ballotid, imgpaths, attrtype, bb, attr2pat, isflip, scale, patchDestDir, queue, queue_progress) = job

        # ((obj imgpatch_i, [obj attrpatch_i, ...], str attrval_i, int side_i, int isflip_i), ...)
        patchTuples = createPatchTuplesMAP(imgpaths,attr2pat,bb,flip=isflip)
        # Remember, attr2pat contains multiple exemplars
        exmpl_imP, firstPat = attr2pat.values()[0][0] # TODO: arbitrary choice, is this ok?
        rszFac = sh.resizeOrNot(firstPat.shape,sh.MAX_PRECINCT_PATCH_DIM);
        sweep=np.linspace(scale,rszFac,num=np.ceil(np.log2(len(attr2pat)))+2)
        sweep = np.array(list(set(list(sweep[sweep <= 1.0]))))

        finalOrder = [] # [(imgpatch_i, attrpatch_i, str attrval_i, int side_i, int isflip_i), ...]
        debug = False

        # 2. process
        #    Workers:
        #      - align with pyramid + prune
        #      - fine-alignment on best result
        #      - store precinct patch in grouping result folder
        #      - store list in grouping meta result file
        for sc in sweep:
            (scores,locs, exemplar_idxs)=dist2patches(patchTuples,sc,debug=debug)
            sidx=np.argsort(scores)
            # reverse for descend
            sidx=sidx[::-1]
            mid=np.ceil(len(sidx)/2.0)
            bestScore=scores[sidx[0]];
            bestLoc=locs[sidx[0]];
            bestExemplarIdx = exemplar_idxs[sidx[0]]
            keepIdx=sidx[0:mid]
            dumpIdx=sidx[mid:len(sidx)]
            dumped=sh.arraySlice(patchTuples,dumpIdx)        
            finalOrder.extend(dumped)
            patchTuples=sh.arraySlice(patchTuples,keepIdx)

        # align patch to top patch
        # patchTuples[0]: Best patch
        # I1: region around the attribute patch
        # P1: an exemplar attribute patch to compare against
        I1=patchTuples[0][0]
        P1=patchTuples[0][1][bestExemplarIdx]
        # finalOrder is of the form:
        #   [(obj imgpatch_i, obj attrpatch_i, str attrval_i, int imgorder_i, int isflip_i), ...]
        finalOrder.extend(patchTuples)
        finalOrder.reverse()

        bestLocG=[round(bestLoc[0]),round(bestLoc[1])]
        # I1c is the purported attrpatch on I1 (voted ballot)
        I1c=I1[bestLocG[0]:bestLocG[0]+P1.shape[0],bestLocG[1]:bestLocG[1]+P1.shape[1]]
        rszFac=sh.resizeOrNot(I1c.shape,sh.MAX_PRECINCT_PATCH_DIM)
        # IO := [transmatrix (?), img, err]
        if P1.shape[0] > I1c.shape[0] or P1.shape[1] > I1c.shape[1]:
            w1 = min(P1.shape[0], I1c.shape[0])
            h1 = min(P1.shape[1], I1c.shape[1])
            P1_a = np.zeros((w1,h1))
            P1_a[0:w1, 0:h1] = P1[0:w1, 0:h1]
            P1 = P1_a
            print 'WEIRD CASE:', P1.shape, I1c.shape
            misc.imsave("_weird_{0}.png".format(str(P1.shape)), P1_a)

        IO=imagesAlign(I1c,P1,trfm_type='rigid',rszFac=rszFac, minArea=np.power(2, 15))
        Ireg = np.nan_to_num(IO[1])
        # RESULT: [[int ballotid, attrtype, dict outdict], ...]

        result = doWriteMAP(finalOrder, Ireg, IO[2], attrtype, patchDestDir, ballotid, bestExemplarIdx)
        queue.put(result)
        queue_progress.put((True, ballotid))
    except Exception as e:
        print 'AAAHH'
        traceback.print_exc()
        queue.put(e.message)
        queue_progress.put((False, ballotid))

def listAttributes(patchesH):
    # tuple ((key=attrType, patchesH tuple))

    attrL = set()
    for val in patchesH.values():
        for (regioncoords, attrtype, attrval, side) in val:
            attrL.add(attrtype)
    
    return list(attrL)

def listAttributesNEW(patchesH):
    """
    Input:
        dict patchesH:
    Output:
        A dict mapping {str attrtype: {str attrval: (bb, int side, k)}}
    """
    # tuple ((key=attrType, patchesH tuple))
    attrMap = {}
    for k in patchesH.keys():
        val=patchesH[k]
        for (bb,attrName,attrVal,side) in val:
            # check if type is in attrMap, if not, create
            
            # [kai] temporary hack for testing
            # attrVal = attrVal + '--' + os.path.basename(k)
            attrMap.setdefault(attrName, {})[attrVal] = (bb, side, k)

    return attrMap

def templateSSWorker_init(queue):
    templateSSWorker.queue = queue

def estimateScale(attr2pat,img2flip,superRegion,rszFac,stopped):
    """
    Input:
        dict attr2pat: maps {str attrval: [[str exmpl_imP, nparray imgpatch_i], ...]}
        tuple superRegion: 
        float rszFac:
        fn stopped:
    Output:
        A scale.
    """
    print 'estimating scale.'
    jobs=[]
    sStep=.05
    sList=[]
    nProc=sh.numProcs()
    #nProc = 1

    queue = mp.Queue()
    pool = mp.Pool(processes=nProc, initializer=templateSSWorker_init, initargs=[queue])

    for attrval in attr2pat.keys():
        jobs.append((attr2pat,attrval,superRegion,sStep,img2flip))

    if nProc < 2:
        # default behavior for non multiproc machines
        for job in jobs:
            if stopped():
                return False
            templateSSWorker.queue = queue
            templateSSWorker(job)
    else:
        print 'using ', nProc, ' processes'

        it = [False]
        def imdone(x):
            it[0] = True
            print "I AM DONE NOW!"
        pool.map_async(templateSSWorker,jobs, callback=lambda x: imdone(it))
        while not it[0]:
            if stopped():
                pool.terminate()
                return False
            time.sleep(.1)

        pool.close()
        pool.join()
    # collect results
    while len(sList) < len(jobs):
        sList.append(queue.get())
    #for job in jobs:
    #    f1=job[5]
    #    s=pickle.load(open(f1))['scale']
    #    sList.append(s)

    print sList
    scale=min(max(sList)+2*sStep,rszFac)
    #scale = 0.95
    return scale

def groupByAttr(bal2imgs, img2page, img2flip, attrName, side, attrMap, 
                patchDestDir, stopped, proj, verbose=False, deleteall=True):
    """
    Input:
        dict bal2imgs: maps {str ballotid: (sidepath_i, ...)}
        dict IMG2PAGE:
        dict IMG2FLIP:
        str attrName: the current attribute type
        int SIDE: 
        dict attrMap: maps {str attrtype: {str attrval: (bb, str side, blankpath)}}
        str patchDestDir: A directory, i.e. 'extracted_precincts-ballottype', stores
            the extracted attribute image patches.
        fn stopped:
        obj proj:
    options:
        bool deleteall: if True, this will first remove all output files
                         before computing.
    """                    
    if deleteall:
        if os.path.exists(patchDestDir): shutil.rmtree(patchDestDir)
    create_dirs(patchDestDir)

    # maps {str attrval: [(str exmpl_imP, obj imagepatch), ...]}
    attr2pat={}
    superRegion=(float('inf'),0,float('inf'),0)
    # attrValMap: {str attrval: (bb, str side, blankpath)}
    attrValMap=attrMap[attrName]
    # 0.) First, grab an exemplar patch for each attrval. Add them to
    #     attr2pat.
    # multexemplars_map: maps {attrtype: {attrval: ((str patchpath_i, str blankpath_i, (x1,y1,x2,y2)), ...)}}
    multexemplars_map = pickle.load(open(pathjoin(proj.projdir_path,
                                                  proj.multexemplars_map),
                                         'rb'))
    exemplar_dict = multexemplars_map[attrName]
    for attrval, exemplars in exemplar_dict.iteritems():
        # Sort, in order to provide a canonical ordering
        exemplars_sorted = sorted(exemplars, key=lambda t: t[0])
        for (patchpath, blankpath, (x1,y1,x2,y2)) in exemplars_sorted:
            P = sh.standardImread(patchpath, flatten=True)
            attr2pat.setdefault(attrval, []).append((blankpath, P))
            superRegion = sh.bbUnion(superRegion, (y1,y2,x1,x2))
    for _attr, patches in attr2pat.iteritems():
        print 'for attr {0}, there are {1} exemplars'.format(_attr, len(patches))
    # 1.) Estimate smallest viable scale (for performance)
    if len(attr2pat)>2:
        scale = estimateScale(attr2pat,img2flip,superRegion,sh.MAX_PRECINCT_PATCH_DIM,stopped)
    else:
        scale = sh.resizeOrNot(P.shape,sh.MAX_PRECINCT_PATCH_DIM);
    print 'ATTR: ', attrName,': using starting scale:',scale
    # 2.) Generate jobs for the multiprocessing
    nProc=sh.numProcs()
    #nProc = 1

    manager = mp.Manager()
    queue = manager.Queue()
    queue_progress = manager.Queue() # Used for MyGauge updates
    pool = mp.Pool(processes=nProc)

    jobs = []
    for ballotid in bal2imgs.keys():
        imgpaths = bal2imgs[ballotid]
        imgpaths_ordered = sorted(imgpaths, key=lambda imP: img2page[imP])
        imgpath_in = imgpaths_ordered[side]
        isflip = img2flip[imgpath_in]
        jobs.append([ballotid, [imgpath_in], attrName, superRegion, attr2pat, isflip, scale,
                     patchDestDir, queue, queue_progress])

    print "Number of jobs:", len(jobs)
    # 3.) Perform jobs.
    if nProc < 2:
        # default behavior for non multiproc machines
        for job in jobs:
            if stopped():
                return False
            groupImagesWorkerMAP(job)
    else:
        print 'using ', nProc, ' processes'
        it = [False]
        def imdone(x):
            it[0] = True
            print "I AM DONE NOW! WOW"
        pool.map_async(groupImagesWorkerMAP,jobs, callback=lambda x: imdone(it))

        i = 0
        while i < len(jobs):
            job_status, job_ballotid = queue_progress.get() # Blocks until value is ready
            if job_status == False:
                print "...Uhoh, ballotid={0} had a grouping failure.".format(job_ballotid)
            if wx.App.IsMainLoopRunning():
                wx.CallAfter(Publisher().sendMessage, "signals.MyGauge.tick", (JOBID_GROUPING_IMGBASED,))
            i += 1

        while not it[0]:
            if stopped():
                print '    UHOH, stopped'
                pool.terminate()
                return False
            time.sleep(.1)

        print "HERE"
        pool.close()
        pool.join()

    print "GOT HERE."
    # list RESULTS: [[int ballotid, attrtype, dict outdict], ...]
    results = []
    cnt = 0
    while cnt < len(jobs):
        res = queue.get()
        if type(res) in (str, unicode):
            print "OH NO, badness happened."
        else:
            results.append(res)
        cnt += 1
        print 'cnt: ', cnt
        
    # TODO: quarantine on grouping errors. For now, just let alignment check handle it
    print 'ATTR: ', attrName, ': done'
    return results

def groupImagesMAP(bal2imgs, partitions_map, partition_exmpls, img2page, img2flip, badballotids,
                   patchesH, grpmode_map, patchDir_root, stopped, proj, verbose=False, deleteall=True):
    """
    Input:
      patchesH: A dict mapping:
                  {str imgpath: List of [(y1,y2,x1,x2), str attrtype, str attrval, str side]},
                where 'side' is either 'front' or 'back'.
      dict GRPMODE_MAP: maps {attrtype: bool is_grp_per_partition}
      list BADBALLOTIDS: List of quarantined/discarded ballot ids. 
      ballotD:
      patchDir_root: Root directory to store voted image attribute patches
      stopped:
      obj proj: 
    Output:
      dict RESULTS. maps {int ballotid: {attrtype: dict outdict}}
      Only contains results for attributes that are NOT consistent within
      each partition.
    """
    # NOTE: assuming each ballot has same number of attributes

    # 1. loop over each attribute
    # 2. perform grouping using unique examples of attribute

    # dict ATTRMAP: maps {attrtype: {attrval: ((y1,y2,x1,x2), side, imgpath)}}
    attrMap=listAttributesNEW(patchesH)
    results = {} 
    for attrtype in attrMap.keys():
        side = attrMap[attrtype].values()[0][1]
        in_bal2imgs = {}
        if grpmode_map[attrtype]:
            # This attribute is consistent within each partition, so
            # don't run grouping.
            print "(Info) Attribute '{0}' is consistent within partitions \
-- not running grouping for this.".format(attrtype)
            continue
        else:
            # Run grouping on /every/ voted ballot, minus quarantined/discarded ballots
            print "...Running grouping on every ballot..."
            in_bal2imgs = bal2imgs.copy()
            for badballotid in badballotids:
                in_bal2imgs.pop(badballotid)
        print "...Running Grouping on Attribute {0}, side {1}...".format(attrtype, side)
        patchDestDir = patchDir_root + '-' + attrtype
        # list RESULT: [[ballotid, attrtype, outdict], ...]
        result = groupByAttr(in_bal2imgs,img2page,img2flip,attrtype, side, attrMap,
                             patchDestDir,stopped, proj,
                             verbose=verbose,deleteall=deleteall)
        for (ballotid, attrtype, outdict) in result:
            results.setdefault(ballotid, {})[attrtype] = outdict
    return results

def is_image_ext(filename):
    IMG_EXTS = ('.bmp', '.png', '.jpg', '.jpeg', '.tif', '.tiff')
    return os.path.splitext(filename)[1].lower() in IMG_EXTS

def create_dirs(*dirs):
    """
    For each dir in dirs, create the directory if it doesn't yet
    exist. Will work for things like:
        foo/bar/baz
    and will create foo, foo/bar, and foo/bar/baz correctly.
    """
    for dir in dirs:
        try:
            os.makedirs(dir)
        except Exception as e:
            pass
