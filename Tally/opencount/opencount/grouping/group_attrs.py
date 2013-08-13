import sys, pickle, pdb, wx, time, copy, random
from os.path import join as pathjoin
import scipy, scipy.misc
import numpy as np
import cv

sys.path.append('../')
import common
import partask
from pixel_reg import shared

_i = 0
                
def cluster_imgpatchesV2(imgpaths, bb_map, init_clusters=None, THRESHOLD=0.95):
    """ Given a list of imgpaths, and bounding boxes for each image,
    cluster the bounding boxes from each image.
    Input:
        list imgpaths:
        dict bb_map: maps {str imgpath: (y1,y2,x1,x2)}
        list init_clusters: An initial set of cluster centers, of the form:
            {imgpath_i: (imgpath_i, bb_i)}
        float THRESHOLD: A cutoff value to use when determining if the patch
            was found. Ranges from [0.0, 1.0], where higher values is 'stricter',
            i.e. THRESHOLD=1.0 means only accept exact matches (not recommended).
            Higher values also means more computation time.
    Output:
        A dict of the form:
            {c_imgpath: [(imgpath_i, bb_i, score), ...}
        where each c_imgpath is the 'center' of a given cluster C.
    """
    clusters = {}
    unlabeled_imgpaths = list(imgpaths)
    while unlabeled_imgpaths:
        curimgpath = unlabeled_imgpaths.pop()
        bb = bb_map[curimgpath]
        I = shared.standardImread(curimgpath, flatten=True)
        _t = time.time()
        print "...calling find_patch_matchesV1..."
        matches = partask.do_partask(findpatchmatches,
                                     unlabeled_imgpaths,
                                     _args=(I,
                                            bb,
                                            bb, THRESHOLD))
        print "...finished find_patch_matchesV1 ({0} s)".format(time.time() - _t)
        # Manually add in I
        matches.append((curimgpath, -1.0, 1.0, None, bb[0], bb[1], bb[2], bb[3], 1.0))
        if matches:
            # 0.) Retrieve best matches from matches (may have multiple
            # matches for the same imagepath)
            print "...number of pre-filtered matches: {0}".format(len(matches))
            bestmatches = {} # maps {imgpath: (imgpath,sc1,sc2,Ireg,y1,y2,x1,x2,rszFac)}
            for (filename,sc1,sc2,Ireg,y1,y2,x1,x2,rszFac) in matches:
                y1, y2, x1, x2 = map(lambda c: int(round(c/rszFac)), (y1, y2, x1, x2))
                if filename not in bestmatches:
                    bestmatches[filename] = (filename,sc1,sc2,y1,y2,x1,x2,rszFac)
                else:
                    old_sc2 = bestmatches[filename][2]
                    if sc2 < old_sc2:
                        bestmatches[filename] = (filename,sc1,sc2,y1,y2,x1,x2,rszFac)
            print "...found {0} matches".format(len(bestmatches))
            # 1.) Handle the best matches
            for _, (filename,sc1,sc2,y1,y2,x1,x2,rszFac) in bestmatches.iteritems():
                if filename in unlabeled_imgpaths:
                    unlabeled_imgpaths.remove(filename)
                clusters.setdefault(curimgpath, []).append((filename, (y1,y2,x1,x2), sc2))
        else:
            print "...Uh oh, no matches found. This shouldnt' have \
happened."
            pdb.set_trace()
    print "...Completed clustering. Found {0} clusters.".format(len(clusters))
    return clusters

def findpatchmatches(imlist, (patch, bb, bbsearch, threshold)):
    return shared.find_patch_matchesV1(patch, bb, imlist, bbSearch=bbsearch,
                                       threshold=threshold)

def group_attributes_V2(project, job_id=None, THRESHOLD=0.95):
    """ Try to cluster all attribute patches from blank ballots into
    groups, in order to reduce operator effort during 'Label Ballot
    Attributes.'
    Output:
        dict mapping {str attrtype: {str c_imgpath: [(imgpath_i, bb_i), ...]}}
    """
    ballot_attrs = pickle.load(open(project.ballot_attributesfile, 'rb'))
    w_img, h_img = project.imgsize
    tmp2imgs = pickle.load(open(project.template_to_images, 'rb'))
    attr_clusters = {} # maps {str attrtype: {str c_imgpath: [(imgpath_i, bb_i, score_i), ...]}}
    bb_mapAll = {} # maps {attrtype: {imgpath: bb}}
    for attr in ballot_attrs:
        if attr['is_digitbased']:
            continue
        x1,y1,x2,y2 = attr['x1'],attr['y1'],attr['x2'],attr['y2']
        x1 = int(round(x1*w_img))
        y1 = int(round(y1*h_img))
        x2 = int(round(x2*w_img))
        y2 = int(round(y2*h_img))
        side = attr['side']
        attrtype = common.get_attrtype_str(attr['attrs'])
        # TODO: Generalize to N-sided elections
        if side == 'front': 
            blank_imgpaths = [paths[0] for paths in tmp2imgs.values()]
        else:
            blank_imgpaths = [paths[1] for paths in tmp2imgs.values()]
        bb_map = {} # maps {imgpath: (y1,y2,x1,x2)}
        for imgpath in blank_imgpaths:
            bb_map[imgpath] = (y1,y2,x1,x2)
        bb_mapAll[attrtype] = bb_map
        clusters = cluster_imgpatchesV2(blank_imgpaths, bb_map, THRESHOLD=THRESHOLD)
        attr_clusters[attrtype] = clusters
    return attr_clusters

def cluster_bkgd(mapping, bb_map=None, D=5, debug_SKIP=False):
    """ Given a mapping {str label: (imgpath_i, ...)}, for each label L,
    generates N exemplar images, where each img in N (hopefully) 
    contains a different backgroung coloring.
    Input:
        dict mapping: {str label: (imgpath_i, ...)}
        dict bb_map: maps {str imgpath: bb}
        int D: A constant threshold used to determine whether or not
               to create a new cluster. For large values of D, this
               will tend to not create new clusters. For very small
               values of D (i.e. ~1-5), this will almost always
               create a new cluster.
    Output:
        A (hopefully) smaller dict mapping {label: (imgpath_i, ...)}.
    """
    if debug_SKIP:
        return dict(mapping)
    if bb_map == None:
        bb_map = {}
    exemplars = {}  # maps {str label: [imgpath_i, ...]}
    clustervals = {} # maps {str label: {str imgpath: float feat}}
    for label, imgpaths in mapping.iteritems():
        print "{0} imgpaths for label {1}".format(len(imgpaths), label)
        clusters = [] # [[(str imgpath_i0, float feat_i0), ...], [(str imgpath_i1, float feat_i1), ...], ...]
        imgpaths = list(imgpaths)
        # 0.) Seed clusters with random center
        # TODO: Use the lightest image
        firstP = imgpaths.pop(random.randrange(0, len(imgpaths)))
        img = scipy.misc.imread(firstP, flatten=True)
        bbFirst = bb_map.get(firstP, None)
        if bbFirst != None:
            img = img[bbFirst[0]:bbFirst[1], bbFirst[2]:bbFirst[3]]
        median = np.median(img)
        clusters.append([(firstP, median), ])
        # 1.) Iteratively either add each I to a previous cluster, or
        #     create a new cluster for I.
        while imgpaths:
            imgP = imgpaths.pop()
            img = scipy.misc.imread(imgP, flatten=True)
            bb = bb_map.get(imgP, None)
            if bb != None:
                img = img[bb[0]:bb[1], bb[2]:bb[3]]
            median = np.median(img)
            best_idx, best_dist = None, None
            for idx, cluster in enumerate(clusters):
                exemplarP, exemplarFeat = cluster[0]
                dist = abs(median - exemplarFeat)
                if dist <= D:
                    if best_idx == None or dist < best_dist:
                        # a.) Merge I into cluster
                        best_idx = idx
                        best_dist = dist
                        cluster.append((imgP, median))
            if best_idx == None:
                # b.) Create a new cluster.
                clusters.append([(imgP, median)])
        # 2.) Emit a single exemplar from each cluster
        for cluster in clusters:
            exemplars.setdefault(label, []).append(cluster[0][0])
    return exemplars

def compute_exemplars(mapping, bb_map=None):
    """ Given a mapping {str label: (imgpath_i, ...)}, extracts a subset
    of the imgpaths {str label: list of imgpaths} such that these
    imgpaths are the best-describing 'exemplars' of the entire input
    mapping.
    Input:
        dict mapping: {label: list of imgpaths}
        dict bb_map: maps {str imgpath: tuple bb}
    Output:
        A (hopefully smaller) dict mapping {label: list of exemplar
        imgpaths}.
    """
    def distance(img, imgpath2):
        h, w = img.shape
        bb = [0, h, 0, w]
        bb2 = bb_map.get(imgpath2, None)
        if bb2 != None:
            bbs2 = {imgpath2: bb2}
            matches = shared.find_patch_matchesV1(img, bb, (imgpath2,), bbSearches=bbs2, threshold=0.1)
        else:
            matches = shared.find_patch_matchesV1(img, bb, (imgpath2,), threshold=0.1)
        matches = sorted(matches, key=lambda t: t[2])
        return matches[0][2]
    def distance2(img, imgpath2):
        """ L2 norm between img1, img2 """
        img2 = shared.standardImread(imgpath2, flatten=True)
        bb2 = bb_map.get(imgpath2, None)
        if bb2 != None:
            img2 = img2[bb2[0]:bb2[1], bb2[2]:bb2[3]]
        img2 = common.resize_img_norescale(img2, (img.shape[1], img.shape[0]))
        diff = np.linalg.norm(img - img2)
        return diff
    def distance3(img, imgpath2):
        """ NCC score between img1, img2. """
        imgCv = cv.fromarray(np.copy(img.astype(np.float32)))
        img2 = shared.standardImread(imgpath2, flatten=True)
        bb2 = bb_map.get(imgpath2, None)
        if bb2 != None:
            img2 = img2[bb2[0]:bb2[2], bb2[2]:bb2[3]]
        img2Cv = cv.fromarray(np.copy(img2.astype(np.float32)))
        outCv = cv.CreateMat(imgCv.height - img2Cv.height+1, imgCv.width - img2Cv.width+1,
                             imgCv.type)
        cv.MatchTemplate(imgCv, img2Cv, outCv, cv.CV_TM_CCOEFF_NORMED)
        return outCv.max()
    def closest_label(imgpath, exemplars):
        mindist = None
        bestmatch = None
        img = shared.standardImread(imgpath, flatten=True)
        bb = bb_map.get(imgpath, None)
        if bb != None:
            img = img[bb[0]:bb[1], bb[2]:bb[3]]
        for label, imgpaths in exemplars.iteritems():
            for imgpathB in imgpaths:
                dist = distance2(img, imgpathB)
                if mindist == None or dist < mindist:
                    bestmatch = label
                    mindist = dist
        return bestmatch, mindist
    mapping = copy.deepcopy(mapping)
    if bb_map == None:
        bb_map = {}
    exemplars = {}
    for label, imgpaths in mapping.iteritems():
        rand_idx = random.choice(range(len(imgpaths)))
        exemplars[label] = [imgpaths.pop(rand_idx)]
    is_done = False
    while not is_done:
        is_done = True
        for label, imgpaths in mapping.iteritems():
            i = 0
            while i < len(imgpaths):
                imgpath = imgpaths[i]
                bestlabel, mindist = closest_label(imgpath, exemplars)
                print 'label should be {0} closest was {1} ({2})'.format(label, bestlabel, mindist)
                if label != bestlabel:
                    exemplars[label].append(imgpath)
                    is_done = False
                    imgpaths.pop(i)
                else:
                    i += 1
    return exemplars

def temp_match(I, bb, imList, bbSearch=None, bbSearches=None, rszFac=0.75,
               padSearch=0.75, padPatch=0.0):
    bb = list(bb)
    if bbSearch != None:
        bbSearch = list(bbSearch)
    if bbSearches != None:
        bbSearches = list(bbSearches)
    matchList = [] # (filename, left,right,up,down)

    I = np.round(shared.fastResize(I,rszFac)*255.)/255;

    bb[0] = bb[0]*rszFac
    bb[1] = bb[1]*rszFac
    bb[2] = bb[2]*rszFac
    bb[3] = bb[3]*rszFac
    [bbOut,bbOff]=shared.expand(bb[0],bb[1],bb[2],bb[3],I.shape[0],I.shape[1],padPatch)
    patchFoo = I[bbOut[0]:bbOut[1],bbOut[2]:bbOut[3]]

    patch = patchFoo[bbOff[0]:bbOff[1],bbOff[2]:bbOff[3]]

    if bbSearch != None:
        bbSearch[0] = bbSearch[0]*rszFac
        bbSearch[1] = bbSearch[1]*rszFac
        bbSearch[2] = bbSearch[2]*rszFac
        bbSearch[3] = bbSearch[3]*rszFac

    for cur_i, imP in enumerate(imList):
        if bbSearches != None:
            bbSearch = map(lambda c: c*rszFac, bbSearches[cur_i])
        I1 = shared.standardImread(imP,flatten=True)
        I1 = np.round(shared.fastResize(I1,rszFac)*255.)/255.
        # crop to region if specified
        if bbSearch != None:
            [bbOut1,bbOff1]=shared.expand(bbSearch[0],bbSearch[1],
                                   bbSearch[2],bbSearch[3],
                                   I1.shape[0],I1.shape[1],padSearch)
            I1=I1[bbOut1[0]:bbOut1[1],bbOut1[2]:bbOut1[3]]
        if I1.shape[0] < patch.shape[0] or I1.shape[1] < patch.shape[1]:
            w_big = max(I1.shape[0], patch.shape[0])
            h_big = max(I1.shape[1], patch.shape[1])
            I1_big = np.zeros((w_big, h_big)).astype('float32')
            I1_big[0:I1.shape[0], 0:I1.shape[1]] = I1
            I1 = I1_big

        patchCv=cv.fromarray(np.copy(patch))
        ICv=cv.fromarray(np.copy(I1))
        outCv=cv.CreateMat(abs(I1.shape[0]-patch.shape[0])+1,abs(I1.shape[1]-patch.shape[1])+1, cv.CV_32F)
        
        cv.MatchTemplate(ICv,patchCv,outCv,cv.CV_TM_CCOEFF_NORMED)
        Iout=np.asarray(outCv)
        
        Iout[Iout==1.0]=0.995; # opencv bug
        
        score1 = Iout.max() # NCC score
        YX=np.unravel_index(Iout.argmax(),Iout.shape)
        i1=YX[0]; i2=YX[0]+patch.shape[0]
        j1=YX[1]; j2=YX[1]+patch.shape[1]
        (err,diff,Ireg)=shared.lkSmallLarge(patch,I1,i1,i2,j1,j2, minArea=np.power(2, 17))
        score2 = err / diff.size # pixel reg score
        if bbSearch != None:
            matchList.append((imP,score1,score2,Ireg,
                              i1+bbOut1[0],i2+bbOut1[0],
                              j1+bbOut1[2],j2+bbOut1[2],rszFac))
        else:
            matchList.append((imP,score1,score2,Ireg,
                              i1,i2,j1,j2,rszFac))

    return matchList
    

def compute_exemplars_fullimg(mapping, MAXCAP=None):
    """ Given a mapping {str label: ((imgpath_i, bb_i),...)}, extracts a subset
    of the imgpaths {str label: (imgpath_i, ...)} such that these
    imgpaths are the best-describing 'exemplars' of the entire input
    mapping. 
    NOTE: bb's here are in [y1,y2,x1,x2] format.
    Input:
        dict mapping: {label: ((imgpath_i, bb_i), ...)}
        int MAXCAP: Maximum number of exemplars per label (optional).
    Output:
        A (hopefully smaller) dict mapping {label: ((imgpath_i, bb_i), ...)}
    """
    def get_closest_ncclk(imgpath, img, bb, imgpaths2, bbs2):
        #t = time.time()
        #print "Running find_patch_matchesV1..."
        if bb == None:
            bb = [0, img.shape[0]-1, 0, img.shape[1]-1]
            bbs2 = None
        #matches = shared.find_patch_matchesV1(img, bb, imgpaths2, bbSearches=bbs2, threshold=0.0, doPrep=False)
        matches = temp_match(img, bb, imgpaths2, bbSearches=bbs2)
        #dur = time.time() - t
        #print "...Finished Running find_patch_matchesV1 ({0} s)".format(dur)
        if not matches:
            print "Uhoh, no matches found for imgpath {0}.".format(imgpath)
            pdb.set_trace()
            return 9999, bb
        matches = sorted(matches, key=lambda t: t[2])
        imgpath, bb, rszFac = (matches[0][0], matches[0][4:8], matches[0][8])
        bb = map(lambda c: int(round(c / rszFac)), bb)
        return (matches[0][2], bb)
    def closest_label(imgpath, bb, exemplars):
        bestlabel = None
        mindist = None
        bbBest = None
        img = shared.standardImread(imgpath, flatten=True)
        for label, tuples in exemplars.iteritems():
            imgpaths2, bbs2 = [], []
            for imgpath2, bb2 in tuples:
                imgpaths2.append(imgpath2)
                bbs2.append(bb2)
            closestdist, bbOut = get_closest_ncclk(imgpath, img, bb, imgpaths2, bbs2)
            if bestlabel == None or closestdist < mindist:
                bestlabel = label
                mindist = closestdist
                bbBest = bbOut
        return bestlabel, mindist, bbBest
    mapping = copy.deepcopy(mapping)
    exemplars = {} # maps {str label: ((imgpath_i, bb_i), ...)}
    for label, tuples in mapping.iteritems():
        imgpaths = [t[0] for t in tuples]
        pathL, scoreL, idxL = common.get_avglightest_img(imgpaths)
        print "Chose starting exemplar {0}, with a score of {1}".format(pathL, scoreL)
        imgpath, bb = tuples.pop(idxL)
        exemplars[label] = [(imgpath, bb)]
    t = time.time()
    print "Making tasks..."
    tasks = make_tasks(mapping)
    init_len_tasks = len(tasks)
    dur = time.time() - t
    print "...Finished Making tasks ({0} s)".format(dur)
    #tasks = make_interleave_gen(*[(imgpath, bb) for (imgpath, bb) in itertools.izip(imgpath, bbs)
    counter = {} # maps {str label: int count}
    is_done = False
    while not is_done:
        is_done = True
        taskidx = 0
        while taskidx < len(tasks):
            if (init_len_tasks > 10) and taskidx % (init_len_tasks / 10) == 0:
                print "."
            label, (imgpath, bb) = tasks[taskidx]
            if MAXCAP != None:
                cur = counter.get(label, 0)
                if cur >= MAXCAP:
                    taskidx += 1
                    continue

            bestlabel, mindist, bbOut = closest_label(imgpath, bb, exemplars)
            if label != bestlabel:
                print "...for label {0}, found new exemplar {1}.".format(label, imgpath)
                tasks.pop(taskidx)
                exemplars[label].append((imgpath, bb))
                if label not in counter:
                    counter[label] = 1
                else:
                    counter[label] += 1

                is_done = False
            else:
                taskidx += 1
    return exemplars

def make_tasks(mapping):
    """ Returns a series of tasks, where each task alternates by label,
    so that we try, say, '1', then '2', then '3', instead of trying
    all the '1's first, followed by all the '2's, etc. Helps to keep
    the running time down.
    Input:
        dict mapping: maps {str label: ((imgpath_i, bb_i), ...)}
    """
    label_tasks = [] # [[...], [...], ...]
    for label, tuples in mapping.iteritems():
        tups = []
        for (imgpath, bb) in tuples:
            tups.append((label, (imgpath, bb)))
        label_tasks.append(tups)
    return interleave(*label_tasks)

def interleave_gen(*lsts):
    """ Inspiration from:
        http://code.activestate.com/recipes/511480-interleaving-sequences/
    """
    for idx in range(0, max(len(lst) for lst in lsts)):
        for lst in lsts:
            try:
                yield lst[idx]
            except IndexError:
                continue

def interleave(*lsts):
    result = []
    for idx in range(0, max(len(lst) for lst in lsts)):
        for lst in lsts:
            try:
                result.append(lst[idx])
            except IndexError:
                continue
    return result

def inc_counter(ctr, k):
    if k not in ctr:
        ctr[k] = 1
    else:
        ctr[k] = ctr[k] + 1
