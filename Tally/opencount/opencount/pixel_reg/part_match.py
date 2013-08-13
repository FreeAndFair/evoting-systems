import multiprocessing as mp
import numpy as np
import imagesAlign as lk
import shared as sh
import time, sys
import distance_transform
import wx
from wx.lib.pubsub import Publisher

sys.path.append('..')

from util import GaugeID

JOBID_GROUPING_DIGITBASED = GaugeID("GROUPING_DIGITBASED")

def dt1(f):
    n = f.size
    D = np.zeros(n)
    R = np.zeros(n)

    k = 0
    v = np.zeros(n)
    z = np.zeros(n+1)

    z[0] = -np.inf
    z[1] = np.inf

    for q in range(1,n-1):
        s1 = ((f[q] + pow(q,2)) - (f[v[k]] + pow(v[k],2)))/(2*q - 2*v[k])
        while s1 <= z[k]:
            k -= 1
            s1 = ((f[q] + pow(q,2)) - (f[v[k]] + pow(v[k],2)))/(2*q - 2*v[k])
        
        k += 1
        v[k] = q
        z[k] = s1
        z[k+1] = np.inf

    k = 1

    for q in range(n-1):
        while z[k+1] < q:
            k += 1
        D[q] = pow((q - v[k]),2) + f[v[k]]
        R[q] = v[k]
        
    return (D,R)

def dt2(I):
    res = np.zeros(I.shape)
    Rx = np.zeros(I.shape)
    Ry = np.zeros(I.shape)
    for i in range(I.shape[0]):
        (D,x) = dt1(I[i,:])
        res[i,:] = D
        Rx[i,:] = x

    for i in range(I.shape[1]):
        (D,y) = dt1(res[:,i])
        res[:,i] = D
        Ry[:,i] = y

    return (res,Rx,Ry)

# partmatch
def pm1(digit_hash,I,nDigits,hspace,hackConstant=250,rejected_hash=None,accepted_hash=None):
    """
    Applies digit-OCR to an image.
    Input:
        dict digit_hash: maps {str digit: img digit_exemplar}
        obj I: image to search over (i.e. voted ballot)
        int nDigits: number of digits to find
        hspace: 
        hackConstant:
        dict rejected_hash: maps {str digit: [((y1,y2,x1,x2), str side_i, bool isflip_i), ...]}
        dict accepted_hash: maps {str digit: [((y1,y2,x1,x2), str side_i, bool isflip_i), ...]}
    """
    # either load previously computed results or compute new
    reject_penalty = .2
    accept_bonus = .2
    matchMat = []
    count = 0;
    keys = digit_hash.keys()
    t0=time.clock()    
    for key in keys:
        Iout = sh.NCC(I,digit_hash[key])
        #misc.imsave("_Iout_{0}.png".format(key), Iout)
        # mask out any part if given by param
        if rejected_hash and rejected_hash.has_key(key):
            for (bbMask, side, isflip) in rejected_hash[key]:
                # TODO: I don't ever use the 'side'. Is it worth removing it
                #       from rejected_hashes, or will it be used downstream?
                h = bbMask[1] - bbMask[0]
                w = bbMask[3] - bbMask[2]
                # Expand the mask-region a little bit
                i1 = max(0,bbMask[0]-(h/4))
                i2 = min(Iout.shape[0], bbMask[0]+(h/4))
                j1 = max(0,bbMask[2]-(w/4))
                j2 = min(Iout.shape[1],bbMask[2]+(w/4))
                Iout[i1:i2,j1:j2]=Iout[i1:i2,j1:j2]-reject_penalty
            #misc.imsave("_Iout_{0}_postmask.png".format(key), Iout)

        if accepted_hash and accepted_hash.has_key(key):
            for (bbMask, side, isflip) in accepted_hash[key]:
                # TODO: I don't ever use the 'side'. Is it worth removing it
                #       from rejected_hashes, or will it be used downstream?
                h = bbMask[1] - bbMask[0]
                w = bbMask[3] - bbMask[2]
                # Expand the mask-region a little bit
                i1 = max(0,bbMask[0]-(h/4))
                i2 = min(Iout.shape[0], bbMask[0]+(h/4))
                j1 = max(0,bbMask[2]-(w/4))
                j2 = min(Iout.shape[1],bbMask[2]+(w/4))
                Iout[i1:i2,j1:j2]=Iout[i1:i2,j1:j2]+accept_bonus
            #misc.imsave("_Iout_{0}_postmask.png".format(key), Iout)

        if len(matchMat) == 0:
            matchMat = np.zeros((Iout.shape[0],Iout.shape[1],len(keys)))

        matchMat[:,:,count] = Iout;
        count += 1

    print 'match time:',time.clock()-t0,'(s)'
    maxResp = np.amax(matchMat,axis=2)
    maxObj = np.argmax(matchMat,axis=2)

    tDP=time.clock()    
    # re-scale resp
    unary = hackConstant*np.power(2-(maxResp+1),2)

    #res = dt2(unary)
    res = distance_transform.dt2(unary)

    # cache bottom up
    M = [[]]*nDigits; 
    Mx = [[]]*nDigits; 
    My = [[]]*nDigits; 
    M[0] = res[0]
    Mx[0] = res[1]
    My[0] = res[2]

    for i in range(1,nDigits-1):
        prev = M[i-1]
        shiftH = np.eye(3)
        shiftH[0,2] = hspace
        prevT = sh.imtransform(prev,shiftH,fillval=prev.max());
        # shift
        #t1=time.clock()    
        # old
        #res0 = dt2(prevT+unary) 
        #print 'old DP time:',time.clock()-t1,'(s)'

        # new cython implementation
        res = distance_transform.dt2(prevT+unary)
        #res = dt2(prevT+unary)
        #print 'diff = ', np.sum(np.abs(res0[0] - res[0]))
        M[i] = res[0]
        Mx[i] = res[1]
        My[i] = res[2]

    prev = M[nDigits-2]
    shiftH = np.eye(3)
    shiftH[0,2] = hspace
    prevT = sh.imtransform(prev,shiftH,fillval=prev.max());
    M[nDigits-1] = prevT+unary
    # get best root position
    rootM = M[nDigits-1]
    YX=np.unravel_index(rootM.argmin(),rootM.shape)
    miny=YX[0]; minx=YX[1];

    # store top down
    optYX = [[]]*nDigits; 
    optYX[nDigits-1] = (miny,minx)
    
    for i in reversed(range(0,nDigits-1)):
        prevMiny = optYX[i+1][0]
        prevMinx = optYX[i+1][1]
        curMx = Mx[i]
        curMy = My[i]
        optYX[i] = (round(curMy[prevMiny,prevMinx-hspace]),
                    round(curMx[prevMiny,prevMinx-hspace]))
        
    patches = []
    bbs = []
    scores = []
    ocr_str = ''
    for i in range(len(optYX)):
        (i1,j1)=optYX[i]

        key = keys[maxObj[(i1,j1)]]
        ocr_str += key
        i2=i1+digit_hash[key].shape[0]
        j2=j1+digit_hash[key].shape[1]
        P = I[i1:i2,j1:j2]
        bbs.append((i1,i2,j1,j2))
        #patches.append(P)
        patches.append(None)
        scores.append(maxResp[(i1,j1)])

    print 'DP time:',time.clock()-tDP,'(s)'
    return (ocr_str,patches,bbs,scores)

# partmatch
def pm2(digit_hash,I,nDigits,hspace,hackConstant=250,rejected_hash=None,accepted_hash=None):
    """
    Applies digit-OCR to an image.
    Input:
        dict digit_hash: maps {str digit: img digit_exemplar}
        obj I: image to search over (i.e. precinct patch from a voted ballot)
        int nDigits: number of digits to find
        hspace: 
        hackConstant:
        dict rejected_hash: maps {str digit: [((y1,y2,x1,x2), str side_i, bool isflip_i), ...]}
        dict accepted_hash: maps {str digit: [((y1,y2,x1,x2), str side_i, bool isflip_i), ...]}
    """
    # either load previously computed results or compute new
    reject_penalty = .2
    accept_bonus = .2
    matchMat = []
    count = 0;
    keys = digit_hash.keys()
    t0=time.clock()    
    for key in keys:
        Iout = sh.NCC(I,digit_hash[key])
        symbol = key[0]
        meta = key[1]
        #misc.imsave("_Iout_{0}.png".format(key), Iout)
        # mask out any part if given by param
        if rejected_hash and rejected_hash.has_key(symbol):
            for (bbMask, side, isflip) in rejected_hash[symbol]:
                # TODO: I don't ever use the 'side'. Is it worth removing it
                #       from rejected_hashes, or will it be used downstream?
                h = bbMask[1] - bbMask[0]
                w = bbMask[3] - bbMask[2]
                # Expand the mask-region a little bit
                i1 = max(0,bbMask[0]-(h/4))
                i2 = min(Iout.shape[0], bbMask[0]+(h/4))
                j1 = max(0,bbMask[2]-(w/4))
                j2 = min(Iout.shape[1],bbMask[2]+(w/4))
                Iout[i1:i2,j1:j2]=Iout[i1:i2,j1:j2]-reject_penalty
            #misc.imsave("_Iout_{0}_postmask.png".format(key), Iout)

        if accepted_hash and accepted_hash.has_key(symbol):
            for (bbMask, side, isflip) in accepted_hash[symbol]:
                # TODO: I don't ever use the 'side'. Is it worth removing it
                #       from rejected_hashes, or will it be used downstream?
                h = bbMask[1] - bbMask[0]
                w = bbMask[3] - bbMask[2]
                # Expand the mask-region a little bit
                i1 = max(0,bbMask[0]-(h/4))
                i2 = min(Iout.shape[0], bbMask[0]+(h/4))
                j1 = max(0,bbMask[2]-(w/4))
                j2 = min(Iout.shape[1],bbMask[2]+(w/4))
                Iout[i1:i2,j1:j2]=Iout[i1:i2,j1:j2]+accept_bonus
            #misc.imsave("_Iout_{0}_postmask.png".format(key), Iout)

        if len(matchMat) == 0:
            matchMat = np.zeros((Iout.shape[0],Iout.shape[1],len(keys)))

        matchMat[:,:,count] = Iout;
        count += 1

    print 'match time:',time.clock()-t0,'(s)'
    maxResp = np.amax(matchMat,axis=2)
    maxObj = np.argmax(matchMat,axis=2)

    tDP=time.clock()    
    # re-scale resp
    unary = hackConstant*np.power(2-(maxResp+1),2)

    #res = dt2(unary)
    res = distance_transform.dt2(unary)

    # cache bottom up
    M = [[]]*nDigits; 
    Mx = [[]]*nDigits; 
    My = [[]]*nDigits; 
    M[0] = res[0]
    Mx[0] = res[1]
    My[0] = res[2]

    for i in range(1,nDigits-1):
        prev = M[i-1]
        shiftH = np.eye(3)
        shiftH[0,2] = hspace
        prevT = sh.imtransform(prev,shiftH,fillval=prev.max());
        # shift
        #t1=time.clock()    
        # old
        #res0 = dt2(prevT+unary) 
        #print 'old DP time:',time.clock()-t1,'(s)'

        # new cython implementation
        res = distance_transform.dt2(prevT+unary)
        #res = dt2(prevT+unary)
        #print 'diff = ', np.sum(np.abs(res0[0] - res[0]))
        M[i] = res[0]
        Mx[i] = res[1]
        My[i] = res[2]

    prev = M[nDigits-2]
    shiftH = np.eye(3)
    shiftH[0,2] = hspace
    prevT = sh.imtransform(prev,shiftH,fillval=prev.max());
    M[nDigits-1] = prevT+unary
    # get best root position
    rootM = M[nDigits-1]
    YX=np.unravel_index(rootM.argmin(),rootM.shape)
    miny=YX[0]; minx=YX[1];

    # store top down
    optYX = [[]]*nDigits; 
    optYX[nDigits-1] = (miny,minx)
    
    for i in reversed(range(0,nDigits-1)):
        prevMiny = optYX[i+1][0]
        prevMinx = optYX[i+1][1]
        curMx = Mx[i]
        curMy = My[i]
        optYX[i] = (round(curMy[prevMiny,prevMinx-hspace]),
                    round(curMx[prevMiny,prevMinx-hspace]))
        
    patches = []
    bbs = []
    scores = []
    ocr_str = ''
    matched_keys = []
    for i in range(len(optYX)):
        (i1,j1)=optYX[i]

        key = keys[maxObj[(i1,j1)]]
        ocr_str += key[0]
        i2=i1+digit_hash[key].shape[0]
        j2=j1+digit_hash[key].shape[1]
        #P = I[i1:i2,j1:j2]
        bbs.append((i1,i2,j1,j2))
        #patches.append(P)
        patches.append(None)
        scores.append(maxResp[(i1,j1)])
        matched_keys.append(key)

    print 'DP time:',time.clock()-tDP,'(s)'
    return (ocr_str,patches,bbs,scores,matched_keys)

def stackMax1(result_hash):
    maxSurf=np.zeros(1); symmax=-1;
    for key in result_hash.keys():
        out=result_hash[key]
        if out.max() > maxSurf.max():
            maxSurf = out
            symmax = key
            
    return (maxSurf,symmax)

def process_one(args):
    try:
        imP, digit_hash,imList,bbSearch,nDigits, hspace, rejected_hashes,accepted_hashes, flipmap, queue_progress = args
        I1 = sh.standardImread(imP,flatten=True)
        if flipmap[imP]:
            I1 = sh.fastFlip(I1)
        # 0.) For Yolo (and perhaps other elections), upside-down voted
        # ballots were problematic. Recall that the ballot straightener
        # will pad the voted ballot with a black border if the B isn't
        # of the specified canonical size (W,H). Currently, the straightener
        # adds the padding to the bottom+right of the image. However, if the
        # voted ballot is upside down, then the padding is added to the 
        # top+left (after undoing the flip), which results in a large shift
        # which our algorithms aren't able to gracefully handle.
        # ROWS, COLS is number of rows/cols removed from remove_border_topleft
        I1, rows, cols = sh.remove_border_topleft(I1)
        #I1=sh.prepOpenCV(I1)
        E_i1 = 0.10  # factor to expand bbSearch by
        E_i2 = 0.33
        E_j1 = 0.05
        E_j2 = 0.05 
        h, w = int(bbSearch[1] - bbSearch[0]), int(bbSearch[3]-bbSearch[2])
        amt_i1 = int(round(E_i1*h))
        amt_i2 = int(round(E_i2*h))
        amt_j1 = int(round(E_j1*w))
        amt_j2 = int(round(E_j2*w))
        if (bbSearch[0] - amt_i1) < 0:
            amt_i1 = bbSearch[0]
        if (bbSearch[1] + amt_i2) > (I1.shape[0]-1):
            amt_i2 = (I1.shape[0]-1 - bbSearch[1])
        if (bbSearch[2] - amt_j1) < 0:
            amt_j1 = bbSearch[2]
        if (bbSearch[3] + amt_j2) > (I1.shape[1]-1):
            amt_j2 = (I1.shape[1]-1 - bbSearch[3])
        bb_patch = [max(0, bbSearch[0]-amt_i1),
                    min(I1.shape[0]-1, bbSearch[1]+amt_i2),
                    max(0, bbSearch[2]-amt_j1),
                    min(I1.shape[1]-1, bbSearch[3]+amt_j2)]
        #I1=I1[bbSearch[0]:bbSearch[1],bbSearch[2]:bbSearch[3]]
        I1_patch = I1[bb_patch[0]:bb_patch[1], bb_patch[2]:bb_patch[3]]

        #if do_flip == False:
        #    misc.imsave('_{0}_{1}_bb.png'.format(os.path.splitext(os.path.split(imP)[1])[0],
        #                                         str(do_flip)),
        #                I1)
        rejected_hash = rejected_hashes.get(imP, None) if rejected_hashes else None
        accepted_hash = accepted_hashes.get(imP, None) if accepted_hashes else None
        # perform matching for all digits
        # return best matching digit
        # mask out 
        # res := (str ocr_str, list patches, list bbs, list scores, list matched_keys)
        res = pm2(digit_hash,I1_patch,nDigits,hspace,rejected_hash=rejected_hash,accepted_hash=accepted_hash)
        #res = pm1(digit_hash,I1,nDigits,hspace,rejected_hash=rejected_hash,accepted_hash=accepted_hash)
        # 1.) Remember to correct for E_i,E_j expansion factor from earlier,
        #     the cropped-out black border (ROWS,COLS), and also to account 
        #     for bbSearch offset.
        newbbs = []
        for bb in res[2]:
            newbb0 = (max(0, bb[0]+bb_patch[0]+rows),
                      min(I1.shape[0]-1, bb[1]+bb_patch[0]+rows),
                      max(0, bb[2]+bb_patch[2]+cols),
                      min(I1.shape[1]-1, bb[3]+bb_patch[2]+cols))
            newbbs.append(newbb0)

        queue_progress.put((True, None))

        return (imP,res[0],res[1],newbbs,res[3])
    except Exception as e:
        traceback.print_exc()
        queue_progress.put((False, (imP, e.message)))
        return False

def digitParse(digit_hash,imList,bbSearch,nDigits, flipmap=None, hspace=20,
               rejected_hashes=None, accepted_hashes=None):
    """Runs NCC-based OCR on the images on imList.
    Input:
        dict digit_hash: maps {(str digit, str meta): img digit_exemplar}
        lst imList: list of imagepaths to search over
        bbSearch: [y1,y2,x1,x2] coords to search on
        nDigits: an integer that specifies how many digits there are.
        dict flipmap: maps {str imgpath: bool isflip}
        dict rejected_hashes: Contains all user rejections for each image,
                              maps:
                                {imgpath: {str digit: [((y1,y2,x1,x2),str side_i,bool isflip_i), ...]}}
        dict accepted_hashes: Contains all user accepts for each image,
                              maps:
                                {imgpath: {str digit: [((y1,y2,x1,x2),str side_i,bool isflip_i), ...]}}
    Output:
        A list of results of the form:
            [(imgpath_i, ocr_str_i, imgpatches_i, patchcoords_i, scores_i), ... ]
    """
    digitList = digit_hash.values();
    patchExample = digitList[0]

    nProc=sh.numProcs()
    #nProc = 1

    manager = mp.Manager()
    queue_progress = manager.Queue() # Used for MyGauge updates

    jobs = [(x,digit_hash,imList,bbSearch,nDigits, hspace, rejected_hashes,accepted_hashes,flipmap, queue_progress) for x in imList]

    if nProc < 2:
        results = []
        for x in imList:
            results.append(process_one((x,digit_hash,imList,bbSearch,nDigits,hspace,rejected_hashes,accepted_hashes,flipmap, queue_progress)))
            job_status, job_metadata = queue_progress.get()
            if job_status == False:
                print "...Uhoh, imP={0} failed in digit-grouping computation.".format(job_metadata[0])
                print "       ErrMsg was:", job_metadata[1]
            if wx.App.IsMainLoopRunning():
                wx.CallAfter(Publisher().sendMessage, "signals.MyGauge.tick", (JOBID_GROUPING_DIGITBASED,))
    else:
        pool = mp.Pool(processes=nProc)
        #results = pool.map(process_one, [(x,digit_hash,imList,bbSearch,nDigits, hspace, rejected_hashes,accepted_hashes,flipmap) for x in  imList])
        result_async = pool.map_async(process_one, jobs)
        
        pool.close()

        i = 0
        while i < len(jobs):
            job_status, job_metadata = queue_progress.get()
            if job_status == False:
                print "...Uhoh, imP={0} failed in digit-grouping computation.".format(job_metadata[0])
                print "       ErrMsg was:", job_metadata[1]
            if wx.App.IsMainLoopRunning():
                wx.CallAfter(Publisher().sendMessage, "signals.MyGauge.tick", (JOBID_GROUPING_DIGITBASED,))
            i += 1

        pool.join()

        results = result_async.get()
    # TODO: Currently, any images that process_one() crashes on is signaled by 
    #       A 'False' value in RESULTS. We should explicitly handle these
    #       cases (perhaps by having the caller quarantine these images).

    return results
