import sys, os, pdb, time, traceback, argparse, threading, multiprocessing, math, Queue, random, hashlib
try: import cPickle as pickle
except ImportError: import pickle
from os.path import join as pathjoin

import wx, numpy as np, cv, scipy.misc
from wx.lib.pubsub import Publisher

sys.path.append('..')

import pixel_reg.shared as shared, util, specify_voting_targets.util_gui as util_gui

from asize import asizeof
from panel_opencount import OpenCountPanel
from grouping import verify_overlays_new, partask

from smartscroll import SmartScrolledGridPanel, CREATE, IDLE, npgray2rgb

"""
TODO:

-  Figure out a better solution than simply saving all digit
   patches to a separate directory? A bit lousy, haha.
"""

"""
Output files:

<projdir>/digitpatch2temp.p

This keeps track of the mapping from digit patch imgpaths to the 
associated blank ballot imgpath:
    {str digitpatchpath: (str templatepath, attrstr, bb, int side)}

<projdir>/digitattrvals_blanks.p

This keeps track of the precinct numbers of all blank ballots:
    {str blankimgpath: {digitattrtype: (str digitval, bb, int side)}}
Note that this is blankimgpath, not blankid.

<projdir>/digit_exemplars_map.p

Maps {str digit: ((regionpath_i, score, bb, patchpath_i), ...)}

<projdir>/extracted_digitpatch_dir/

Stores the image patch around each digit region. If the digitattr is
partition-consistent, then only one patch from each partition is stored.
If the digitattr varies within partitions, then a random sample of K
patches is saved from each partition.

"""

# Fraction of ballots to add from each partition when considering a
# digitbased attribute that varies within a partition.
GRP_MODE_ALL_BALLOTS_NUM = 0.2

GRP_MODE_ALL_BALLOTS_NUM_MIN = 10
GRP_MODE_ALL_BALLOTS_NUM_MAX = 750

GLOBAL_ID = 0

class LabelDigitsPanel(OpenCountPanel):
    def __init__(self, parent, *args, **kwargs):
        OpenCountPanel.__init__(self, parent, *args, **kwargs)

        self.gridpanel = TempMatchGrid(self)

        btn_pageup = wx.Button(self, label="Page Up")
        btn_pageup.Bind(wx.EVT_BUTTON, self.onButton_pageup)
        btn_pagedown = wx.Button(self, label="Page Down")
        btn_pagedown.Bind(wx.EVT_BUTTON, self.onButton_pagedown)
        btn_pageup.Hide()    # These haven't been
        btn_pagedown.Hide()  # implemented yet.
        
        btn_zoomin = wx.Button(self, label="Zoom In")
        btn_zoomin.Bind(wx.EVT_BUTTON, lambda evt: self.gridpanel.zoomin())
        btn_zoomout = wx.Button(self, label="Zoom Out")
        btn_zoomout.Bind(wx.EVT_BUTTON, lambda evt: self.gridpanel.zoomout())

        btn_sort = wx.Button(self, label="Sort Cells")
        btn_sort.Bind(wx.EVT_BUTTON, lambda evt: self.gridpanel.sort_cells())

        btn_sizer = wx.BoxSizer(wx.HORIZONTAL)
        btn_sizer.AddMany([(btn_pageup,), (btn_pagedown,), ((20,0,),), (btn_zoomin,), (btn_zoomout,), ((20,0),), (btn_sort,)])

        btn_create = wx.Button(self, label="Create")
        btn_create.Bind(wx.EVT_BUTTON, lambda evt: self.gridpanel.set_mode(CREATE))
        btn_modify = wx.Button(self, label="Modify")
        btn_modify.Bind(wx.EVT_BUTTON, lambda evt: self.gridpanel.set_mode(IDLE))
        
        btnmode_sizer = wx.BoxSizer(wx.HORIZONTAL)
        btnmode_sizer.AddMany([(btn_create,), (btn_modify,)])

        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.sizer.Add(self.gridpanel, proportion=1, border=10, flag=wx.EXPAND | wx.ALL)
        self.sizer.Add(btn_sizer, flag=wx.ALIGN_CENTER)
        self.sizer.Add(btnmode_sizer, flag=wx.ALIGN_CENTER)
        self.SetSizer(self.sizer)
        self.Layout()

    def start(self, proj, *args, **kwargs):
        self.proj = proj
        self.statefile = pathjoin(self.proj.projdir_path, '_state_labeldigits.p')
        self.proj.addCloseEvent(self.save_session)

        if os.path.exists(self.statefile):
            self.restore_session(pickle.load(open(self.statefile, 'rb')))
            return

        extracted_digitpatches_fulldir = pathjoin(proj.projdir_path,
                                                  proj.extracted_digitpatch_dir)
        digit_ex_fulldir = pathjoin(proj.projdir_path, proj.digit_exemplars_outdir)
        precinctnums_fullpath = pathjoin(proj.projdir_path, proj.precinctnums_outpath)
        if not os.path.exists(extracted_digitpatches_fulldir):
            print "Extracting Digit Patches..."
            t = time.time()
            # TODO: Add progress bar here
            patch2temp = do_extract_digitbased_patches(self.proj,
                                                       GRP_MODE_ALL_BALLOTS_NUM,
                                                       GRP_MODE_ALL_BALLOTS_NUM_MIN,
                                                       GRP_MODE_ALL_BALLOTS_NUM_MAX)
            print "...Finished Extracting Digit Patches ({0:.4f} s).".format(time.time() - t)
            pickle.dump(patch2temp, open(pathjoin(proj.projdir_path,
                                                  proj.digitpatch2temp),
                                         'wb'))
        imgpaths = []
        for dirpath, dirnames, filenames in os.walk(extracted_digitpatches_fulldir):
            for imgname in [f for f in filenames if util_gui.is_image_ext(f)]:
                imgpaths.append(os.path.join(dirpath, imgname))

        I = scipy.misc.imread(imgpaths[0])
        w, h = I.shape[1], I.shape[0]

        def get_num_digits(proj):
            # list ATTRS: [dict attrbox_marsh, ...]
            attrs = pickle.load(open(proj.ballot_attributesfile))
            for attr in attrs:
                if attr['is_digitbased']:
                    return attr['num_digits']
            raise Exception("Couldn't find any digit-based attributes?!")

        self.gridpanel.set_object_limit(get_num_digits(self.proj))

        self.gridpanel.outdir = pathjoin(self.proj.projdir_path, 'labeldigits_tempmatch_outdir')
        self.gridpanel.start(imgpaths, cellsize=(w, h), rows_page=4, lookahead=2)

        self.Layout()

    def stop(self):
        if not self.proj:
            # We haven't been run before, perhaps because this election has no
            # digit-based attributes
            return
        self.proj.removeCloseEvent(self.save_session)
        self.save_session()
        self.export_results()

    def export_results(self):
        print "(LabelDigits) Exporting results."
        digitpatch2temp = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                    self.proj.digitpatch2temp)))
        
        digitattrvals_blanks = {}  # maps {str templatepath: {digitattrtype: (str precinctstr, bb, side)}}
        # Oddly enough, I don't think anything uses the SCORE or PATCHPATH entries
        # of DIGITEXEMPLARS_MAP. Let's not fill them in.
        digitexemplars_map = {} # maps {str digit: ((regionpath_i, score, bb, patchpath_i), ...)} where BB := [y1,y2,x1,x2]

        for cellid, boxes in self.gridpanel.cellid2boxes.iteritems():
            # TODO: Assumes precinct nums are oriented horizontally.
            boxes_sorted = sorted(boxes, key=lambda b: b[0])
            precinctstr = "".join([b[-1] for b in boxes_sorted])

            regionpath = self.gridpanel.cellid2imgpath[cellid]
            temppath, attrstr, bb, side = digitpatch2temp[regionpath]
            digitattrvals_blanks.setdefault(temppath, {})[attrstr] = (precinctstr, bb, side)

            for box in boxes_sorted:
                if box[0] == None:
                    # This is a manual-labeled cell
                    continue
                # digitexemplars_map expects the bb to be: [y1, y2, x1, x2]
                bb = [box[1], box[3], box[0], box[2]]
                digitval = box[-1]
                digitexemplars_map.setdefault(digitval, []).append((regionpath, None, bb, None))

        pickle.dump(digitattrvals_blanks, open(pathjoin(self.proj.projdir_path,
                                                        self.proj.digitattrvals_blanks),
                                               'wb'))
        de_mapP = pathjoin(self.proj.projdir_path,
                           self.proj.digit_exemplars_map)
        pickle.dump(digitexemplars_map, open(de_mapP, 'wb'))

    def get_state(self):
        state = {'state_grid': self.gridpanel.get_state()}
        return state
    def restore_session(self, state):
        state_grid = state['state_grid']
        self.gridpanel.restore_state(state_grid)
    def save_session(self):
        if self.statefile:
            print "(LabelDigits) Saving state to statefile:", self.statefile
            pickle.dump(self.get_state(), open(self.statefile, 'wb'))

    def onButton_pageup(self, evt):
        pass
    def onButton_pagedown(self, evt):
        pass

    def invoke_sanity_checks(self, *args, **kwargs):
        """ Code that actually calls each sanity-check with application
        specific arguments. Outputs a list of statuses, like:

            [(bool isOk, bool isFatal, str msg, int id_flag, obj data), ...]

        This should be overridden by each class.
        """
        # Ensure that each cell has the correct number of labeled digits
        flag_ok = True
        for cellid in self.gridpanel.cellid2imgpath.keys():
            boxes = self.gridpanel.cellid2boxes.get(cellid, [])
            if len(boxes) != self.gridpanel.NUM_OBJECTS:
                flag_ok = False
                break
        fail_msg = "One or more of the digit patches does not have enough \
labeled digits - you must label all {0} digits on each patch to proceed. \n\n\
Try clicking the 'Sort Cells' button to easily find the patches that are missing \
digit labels.".format(self.gridpanel.NUM_OBJECTS)
        return [(flag_ok, True, fail_msg, 0, None)]

class TempMatchGrid(SmartScrolledGridPanel):
    DIGIT_TEMPMATCH_ID = util.GaugeID("LabelDigitTempMatchID")

    def __init__(self, parent, *args, **kwargs):
        SmartScrolledGridPanel.__init__(self, parent, *args, **kwargs)

        # int NUM_OBJECTS: Number of 'digits' expected in each ImagePanel.
        # If None, then it is unbounded.
        self.NUM_OBJECTS = None
        # float TM_THRESHOLD: Template matching threshold, in range [0.0, 1.0]. A
        # threshold of 1.0 requires matches to be perfect (strictest), whereas a
        # threshold of 0.0 is the loosest.
        self.TM_THRESHOLD = 0.84
        # Sets num. of processes to use for template matching (multiprocessing)
        #    '1': Single process, don't use multiprocessing
        #    None: Use number of processes equal to number of CPU cores (good default value)
        self.NPROCS = None

        self.outdir = 'tempmatchgrid_outdir'

    def get_state(self, *args, **kwargs):
        state = SmartScrolledGridPanel.get_state(self, *args, **kwargs)
        state['NUM_OBJECTS'] = self.NUM_OBJECTS
        state['TM_THRESHOLD'] = self.TM_THRESHOLD
        state['NPROCS'] = self.NPROCS
        state['outdir'] = self.outdir
        return state

    def set_object_limit(self, k):
        """ Sets the max number of objects on each image. """
        self.NUM_OBJECTS = k

    def on_box_create(self, cellid, box, npimg, label=None):
        w, h = npimg.shape[1], npimg.shape[0]
        x1, y1 = max(0, box[0]), max(0, box[1])
        x2, y2 = min(w, box[2]), min(h, box[3])
        patch = npimg[y1:y2, x1:x2]

        dlg = LabelDigitPatchDialog(self, patch)
        status = dlg.ShowModal()
        if status == wx.ID_CANCEL:
            return

        label = dlg.label
        
        # Determine which images to run template matching on
        imgpaths_in = []
        for imgpath, cellid in self.imgpath2cellid.iteritems():
            if cellid in self.cellids_manual:
                continue
            boxes = self.cellid2boxes.get(cellid, [])
            if self.NUM_OBJECTS == None or (len(boxes) < self.NUM_OBJECTS):
                imgpaths_in.append(imgpath)

        m = multiprocessing.Manager()
        progress_queue = m.Queue()
        t_listen = ThreadUpdateGauge(progress_queue, self.DIGIT_TEMPMATCH_ID)
        t_listen.start()

        numtasks = len(imgpaths_in)
        gauge = util.MyGauge(self, 1, msg="Running Template Matching...",
                             job_id=self.DIGIT_TEMPMATCH_ID)
        gauge.Show()
        wx.CallAfter(Publisher().sendMessage, "signals.MyGauge.nextjob", (numtasks, self.DIGIT_TEMPMATCH_ID))

        print "(TempMatchGrid) Running template matching on {0} images for label: '{1}'".format(len(imgpaths_in), label)
        do_tempmatch_async(patch, imgpaths_in, lambda res: self.on_tempmatch_done(res, label, patch, t_listen, self.DIGIT_TEMPMATCH_ID), self.outdir,
                           THRESHOLD=self.TM_THRESHOLD, NPROCS=self.NPROCS, jobid=self.DIGIT_TEMPMATCH_ID, progress_queue=progress_queue)

    def on_tempmatch_done(self, matches, label, exemplarimg, t_listen=None, jobid=None):
        """
        Input:
            list MATCHES: MATCHES: [(imgpath, score1, score2, patch, i1, i2, j1, j2, rszFac), ...]
        """
        def are_any_too_close(B, boxes):
            """ Return True if B is too close to any box in BOXES. """
            area_B = abs((B[0] - B[2]) * (B[1] - B[3]))
            for box in boxes:
                minarea = min(abs((box[0] - box[2]) * (box[1] - box[3])),
                              area_B)
                if minarea == 0:
                    return False
                commonarea = get_common_area((B[1], B[3], B[0], B[2]),
                                             (box[1], box[3], box[0], box[2]))
                if (commonarea / float(minarea)) >= 0.5:
                    return True
            return False
        print "(TempMatchGrid) on_tempmatch_done: Found {0} matches.".format(len(matches))
        if t_listen != None:
            t_listen.stop_running.set()
        if jobid != None:
            wx.CallAfter(Publisher().sendMessage, "signals.MyGauge.done", (jobid,))

        imgpaths = []
        patch2match = {} # maps {str patchpath: (int cellid, float sc2, x1, y1, x2, y2)}
        for (imgpath,sc1,sc2,patchpath,y1,y2,x1,x2,rszFac) in matches:
            x1, y1, x2, y2 = [int(round(coord / rszFac)) for coord in (x1, y1, x2, y2)]
            cellid = self.imgpath2cellid[imgpath]
            boxes_cell = self.cellid2boxes.get(cellid, [])
            if self.NUM_OBJECTS != None and len(boxes_cell) >= self.NUM_OBJECTS:
                continue
            if are_any_too_close((x1, y1, x2, y2), boxes_cell):
                continue
            imgpaths.append(patchpath)
            cellid = self.imgpath2cellid[imgpath]
            patch2match[patchpath] = (cellid, sc2, x1, y1, x2, y2)

        # == Now, verify the found-matches via overlay-verification
        self.f = verify_overlays_new.CheckImageEqualsFrame(self, imgpaths, exemplarimg, lambda res: self.on_verify_done(res, patch2match, label))
        self.f.Maximize()
        self.f.Show()

    def on_verify_done(self, verify_results, patch2match, label):
        """
        Input:
            dict VERIFY_RESULTS: maps {tag: [patchpath_i, ...]}
            dict PATCH2MATCH: maps {str patchpath: (int cellid, float sc2, x1, y1, x2, y2)}
        """
        self.f.Close()
        YES = verify_overlays_new.CheckImageEquals.TAG_YES
        NO = verify_overlays_new.CheckImageEquals.TAG_NO
        num_added = 0
        for tag, patchpaths in verify_results.iteritems():
            if tag == NO:
                # The user said that these elements are not relevant
                for patchpath in patchpaths:
                    os.remove(patchpath)
            elif tag == YES:
                for patchpath in patchpaths:
                    cellid, sc, x1, y1, x2, y2 = patch2match[patchpath]
                    self.cellid2boxes.setdefault(cellid, []).append([x1, y1, x2, y2, label])
                    num_added += 1

        print "(TempMatchGrid) Added {0} matches final.".format(num_added)
        self.Refresh()

def get_common_area(bb1, bb2):
    """ Returns common area between bb1, bb2.
    Input:
        bb1: (y1,y2,x1,x2)
        bb2: (y1,y2,x1,x2)
    Output:
        area.
    """
    def common_segment(seg1, seg2):
        """ Returns the segment common to both seg1, seg2:
        Input:
            seg1, seg2: tuples (a1, a2)
        Output:
            A tuple (b1, b2), or None if there's no intersection.
        """
        # First make seg1 to the left of seg2
        if seg2[0] < seg1[0]:
            tmp = seg1
            seg1 = seg2
            seg2 = tmp
        if seg2[0] < seg1[1]:
            outA = seg2[0]
            outB = min(seg1[1], seg2[1])
            return (outA, outB)
        else:
            return None
    if bb1[3] > bb2[3]:
        # Make bb1 to the left of bb2
        tmp = bb1
        bb1 = bb2
        bb2 = tmp
    y1a,y2a,x1a,x2a = bb1
    y1b,y2b,x1b,x2b = bb2
    w_a, h_a = abs(x1a-x2a), abs(y1a-y2a)
    w_b, h_b = abs(x1b-x2b), abs(y1b-y2b)
    segw_a = x1a, x1a+w_a
    segh_a = y1a-h_a, y1a
    segw_b = x1b, x1b+w_b
    segh_b = y1b-h_b, y1b
    cseg_w = common_segment(segw_a, segw_b)
    cseg_h = common_segment(segh_a, segh_b)
    if cseg_w == None or cseg_h == None:
        return 0.0
    else:
        return abs(cseg_w[0]-cseg_w[1]) * abs(cseg_h[0]-cseg_h[1])

def a_equal(a, b, T=1e-3):
    return abs(a - b) <= T
        
def test_get_common_area():
    tests = [] # [(A, B, float expected), ...]
    tests.append(( (1, 4, 4, 1), (9, 9, 18, 4), 0.0))
    tests.append(( (1, 4, 4, 1), (1, 9, 3, 7), 0.0))
    tests.append(( (1, 3, 3, 1), (1, 3, 3, 1), 4.0))
    tests.append(( (1, 3, 3, 1), (2, 3, 3, 1), 2.0))
    tests.append(( (1, 3, 3, 1), (2, 3, 100, 100), 2.0))
    tests.append(( (2, 100, 40, 0), (2, 100, 40, 0), 3800.0))
    tests.append(( (0,0,0,0), (0,0,0,0), 0.0))
    tests.append(( (0,0,0,0), (1,1,1,1), 0.0))

    num_failed = 0
    for i, (A, B, expected) in enumerate(tests):
        area = common_area(A, B)
        bb1 = (A[1], A[3], A[0], A[2])
        bb2 = (B[1], B[3], B[0], B[2])
        area0 = get_common_area(bb1, bb2)
        area1 = get_common_area(bb2, bb1)
        if area0 != area1:
            print "Test {0} Error: area0 != area1: area0={0:.5f} area1={0:.5f}".format(area0, area1)
            print "    A: {0}    B: {1}".format(A, B)
        elif not a_equal(area0, expected):
            print "Test {0} Failed: Got '{1:.5f}', expected '{2:.5f}'".format(i, area0, expected)
            print "    A: {0}    B :{1}".format(A, B)
            num_failed += 1

    print "Done. {0} / {1} Tests passed.".format(len(tests) - num_failed, len(tests))

def do_extract_digitbased_patches(proj, C, MIN, MAX):
    """ Extracts all digit-based attribute patches, and stores them
    in the proj.extracted_digitpatch_dir directory.
    Input:
        obj proj:
        (The following args are used if the digitattr varies within a
         partition)
        int C: Suggested fraction of ballots to randomly sample.
        int MIN, MAX: Min./Max. number of ballots to randomly sample.
    Output:
        Returns a dict mapping {str patchpath: (imgpath, attrtype, bb, int side)}
    """
    # all_attrtypes is a list of dicts (marshall'd AttributeBoxes)
    all_attrtypes = pickle.load(open(proj.ballot_attributesfile, 'rb'))
    digit_attrtypes = []  # list of (attrs,x1,y1,x2,y2,side)
    for attrbox_dict in all_attrtypes:
        if attrbox_dict['is_digitbased']:
            attrs = attrbox_dict['attrs']
            x1 = attrbox_dict['x1']
            y1 = attrbox_dict['y1']
            x2 = attrbox_dict['x2']
            y2 = attrbox_dict['y2']
            side = attrbox_dict['side']
            is_part_consistent = attrbox_dict['grp_per_partition']
            digit_attrtypes.append((attrs,x1,y1,x2,y2,side,is_part_consistent))
    if len(digit_attrtypes) >= 2:
        raise Exception("Only one digit attribute may exist.")
    bal2imgs = pickle.load(open(proj.ballot_to_images, 'rb'))
    # PARTITIONS_MAP: maps {int partitionID: [int ballotID, ...]}
    partitions_map = pickle.load(open(pathjoin(proj.projdir_path,
                                               proj.partitions_map), 'rb'))
    img2page = pickle.load(open(pathjoin(proj.projdir_path,
                                         proj.image_to_page), 'rb'))
    img2flip = pickle.load(open(pathjoin(proj.projdir_path,
                                         proj.image_to_flip), 'rb'))
    if digit_attrtypes[0][6]:
        # Digit attr is consistent within each partition -- only choose
        # one ballot from each partition
        chosen_bids = set()
        for partitionid, ballotids in partitions_map.iteritems():
            if ballotids:
                chosen_bids.add(ballotids[0])
        print "...Digit attribute is consistent w.r.t partitions, chose {0} ballots".format(len(chosen_bids))
    else:
        # Randomly choose ballots from the election.
        candidate_balids = sum(partitions_map.values(), [])
        N = max(min(int(round(len(candidate_balids) * C)), MAX), MIN)
        N = min(N, len(candidate_balids)) # If MIN < len(B), avoid oversampling
        chosen_bids = set(random.sample(candidate_balids, N))
        print "...Digit attribute is NOT consistent w.r.t partitions, chose {0} ballots".format(len(chosen_bids))

    partition_exmpls = pickle.load(open(pathjoin(proj.projdir_path,
                                                 proj.partition_exmpls), 'rb'))
    tasks = [] # list [(int ballotID, [imgpath_side0, ...]), ...]
    for ballotid in chosen_bids:
        imgpaths = bal2imgs[ballotid]
        imgpaths_ordered = sorted(imgpaths, key=lambda imP: img2page[imP])
        tasks.append((ballotid, imgpaths_ordered))
    return partask.do_partask(extract_digitbased_patches,
                              tasks,
                              _args=(digit_attrtypes, proj, img2flip),
                              combfn=_my_combfn,
                              init={},
                              pass_idx=True,
                              N=None)

def _my_combfn(results, subresults):
    return dict(results.items() + subresults.items())

def extract_digitbased_patches(tasks, (digit_attrtypes, proj, img2flip), idx):
    i = 0
    outdir = pathjoin(proj.projdir_path, proj.extracted_digitpatch_dir)
    patch2temp = {} # maps {str patchpath: (imgpath, attrtype, bb, int side)}
    for (attrs,x1,y1,x2,y2,side,is_part_consistent) in digit_attrtypes:
        for templateid, imgpaths in tasks:
            imgpath = imgpaths[side]
            I = cv.LoadImage(imgpath, cv.CV_LOAD_IMAGE_GRAYSCALE)
            if img2flip[imgpath]:
                cv.Flip(I, I, flipMode=-1)
            cv.SetImageROI(I, (x1, y1, x2-x1, y2-y1))
            attrs_sorted = sorted(attrs)
            attrs_sortedstr = '_'.join(attrs_sorted)
            '''
            # Next images in two levels of subdirectories
            id_hash = hashlib.sha1(str(templateid)).hexdigest()
            subdir0 = id_hash[:2]
            subdir1 = id_hash[2:4]
            '''
            try:
                os.makedirs(pathjoin(outdir, attrs_sortedstr))
            except:
                pass
            #outfilename = 'balid_{0}.png'.format(templateid)
            outfilename = '{0}_{1}_exemplar.png'.format(idx, i)
            outfilepath = pathjoin(outdir,
                                   attrs_sortedstr,
                                   outfilename)
            cv.SaveImage(outfilepath, I)
            bb = (y1, y2, x1, x2)
            patch2temp[outfilepath] = (imgpath, attrs_sortedstr, bb, side)
            i += 1
    return patch2temp

def do_tempmatch_async(patch, imgpaths, callback, outdir,
                       THRESHOLD=0.8, NPROCS=None,
                       jobid=None, progress_queue=None):
    """
    Note that this method returns immediately. Once the processing is done,
    then the input CALLBACK is called.
    Input:
        nparray PATCH:
        list IMGPATHS:
        fn CALLBACK:
        str OUTDIR:
            Directory to temporarily store extracted patch matches, for overlay
            verification.
        float THRESHOLD: [0.0, 1.0]
            Threshold value to use for template matching. '1.0' means only
            accept perfect matches.
    Output: (callback)
        list MATCHES: MATCHES: [(imgath, score1, score2, str matchpatchpath, i1, i2, j1, j2, rszFac), ...]
    """
    if NPROCS == None:
        NPROCS = multiprocessing.cpu_count()
    class ThreadDoTempMatch(threading.Thread):
        def __init__(self, img1, imgpaths, callback, THRESHOLD, *args, **kwargs):
            """ Search for img1 within images in imgpaths. """
            threading.Thread.__init__(self, *args, **kwargs)
            self.img1 = img1
            self.imgpaths = imgpaths
            self.callback = callback
            self.THRESHOLD = THRESHOLD

        def run(self):
            global GLOBAL_ID
            h, w =  self.img1.shape
            bb = [0, h-1, 0, w-1]
            # list MATCHES: [(imgath, score1, score2, patch, i1, i2, j1, j2, rszFac), ...]
            t = time.time()

            imgpatch = self.img1.astype('float32') / 255.0
            
            if NPROCS == 1:
                print "(ThreadDoTempMatch): Using 1 process (TM_THRESHOLD={0}).".format(self.THRESHOLD)
                matches = shared.find_patch_matchesV1(imgpatch, bb[:], self.imgpaths, threshold=self.THRESHOLD,
                                                      output_Ireg=False,
                                                      save_patches=True, outdir=outdir, outid_start=GLOBAL_ID,
                                                      jobid=jobid, progress_queue=progress_queue)
            else:
                print "(ThreadDoTempMatch): Using {0} processes. (TM_THRESHOLD={1})".format(NPROCS, self.THRESHOLD)
                procs = [] # [(Process p, int numimgs), ...]
                if progress_queue != None:
                    manager = multiprocessing.Manager()
                else:
                    manager = progress_queue._manager
                queue = manager.Queue()
                t_start = time.time()
                step = int(math.ceil(len(self.imgpaths) / float(NPROCS)))
                for procnum in xrange(NPROCS):
                    i_start = procnum * step
                    i_end = i_start + step
                    if procnum == NPROCS - 1:
                        imgpaths_in = self.imgpaths[i_start:]
                    else:
                        imgpaths_in = self.imgpaths[i_start:i_end]
                    outdir_in = os.path.join(outdir, "proc_{0}".format(procnum))
                    p = multiprocessing.Process(target=mp_patchmatch,
                                                args=(queue, 
                                                      imgpatch, bb[:], imgpaths_in),
                                                kwargs={'output_Ireg': False,
                                                        'save_patches': True,
                                                        'outdir': outdir_in,
                                                        'outid_start': GLOBAL_ID,
                                                        'jobid': jobid, 'progress_queue': progress_queue})
                    p.start()
                    procs.append((p, len(imgpaths_in)))

                matches = []
                for i, (proc, numimgs) in enumerate(procs):
                    proc.join()
                    dur = time.time() - t_start
                    p_matches = queue.get()
                    print "(Process_{0}) Finished temp matching, got {1} matches ({2:.4f}s, {3} images total)".format(i, len(p_matches), dur, numimgs)
                    matches.extend(p_matches)
                                                                                          
            dur = time.time() - t
            print "DONE with temp matching. Found: {0} matches    ({1:.4f}s, {2:.5f}s per image)".format(len(matches), dur, dur / float(len(self.imgpaths)))
            GLOBAL_ID += len(matches)
            matches_size = asizeof(matches)
            print "    sizeof(matches): {0} bytes ({1:.4f} MB)".format(matches_size, matches_size / 1e6)
            wx.CallAfter(self.callback, matches)

    t = ThreadDoTempMatch(patch, imgpaths, callback, THRESHOLD)
    t.start()

class ThreadUpdateGauge(threading.Thread):
    def __init__(self, progress_queue, jobid, *args, **kwargs):
        threading.Thread.__init__(self, *args, **kwargs)
        self.progress_queue, self.jobid = progress_queue, jobid
        self.stop_running = threading.Event()

    def run(self):
        while not self.stop_running.is_set():
            try:
                self.progress_queue.get(True, 2)
                wx.CallAfter(Publisher().sendMessage, "signals.MyGauge.tick", (self.jobid,))
            except Queue.Empty:
                pass

def mp_patchmatch(queue, *args, **kwargs):
    matches = shared.find_patch_matchesV1(*args, **kwargs)
    queue.put(matches)

class LabelDigitPatchDialog(wx.Dialog):
    def __init__(self, parent, patch, *args, **kwargs):
        wx.Dialog.__init__(self, parent, title="Digit Value?", 
                           style=wx.CAPTION | wx.RESIZE_BORDER | wx.MAXIMIZE_BOX | wx.MINIMIZE_BOX | wx.SYSTEM_MENU, *args, **kwargs)
        
        self.label = None

        w, h = patch.shape[1], patch.shape[0]
        patch_rgb = npgray2rgb(patch)
        bitmap = wx.BitmapFromBuffer(w, h, patch_rgb)
        staticbitmap = wx.StaticBitmap(self, bitmap=bitmap)

        stxt = wx.StaticText(self, label="What digit is this?")
        self.txtctrl = wx.TextCtrl(self, style=wx.TE_PROCESS_ENTER)
        self.txtctrl.Bind(wx.EVT_TEXT_ENTER, lambda evt: self.onButton_ok(None))

        txt_sizer = wx.BoxSizer(wx.HORIZONTAL)
        txt_sizer.AddMany([(stxt,), (self.txtctrl,)])

        btn_ok = wx.Button(self, label="Ok")
        btn_ok.Bind(wx.EVT_BUTTON, self.onButton_ok)
        btn_cancel = wx.Button(self, label="Cancel")
        btn_cancel.Bind(wx.EVT_BUTTON, self.onButton_cancel)
        btn_sizer = wx.BoxSizer(wx.HORIZONTAL)
        btn_sizer.AddMany([(btn_ok,), (btn_cancel,)])

        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.sizer.Add(staticbitmap, flag=wx.ALIGN_CENTER)
        self.sizer.Add(txt_sizer)
        self.sizer.Add(btn_sizer, flag=wx.ALIGN_CENTER)
        self.SetSizer(self.sizer)
        self.Fit()

        self.Bind(wx.EVT_KEY_DOWN, self.onKeyDown)
        self.txtctrl.Bind(wx.EVT_KEY_DOWN, self.onKeyDown)

        self.txtctrl.SetFocus()

    def onButton_ok(self, evt):
        self.label = self.txtctrl.GetValue()
        if not self.label:
            dlg = wx.MessageDialog(self, message="Please enter a digit value.", style=wx.OK)
            dlg.ShowModal()
            return
        self.EndModal(wx.ID_OK)

    def onButton_cancel(self, evt):
        self.EndModal(wx.ID_CANCEL)

    def onKeyDown(self, evt):
        keycode = evt.GetKeyCode()
        if keycode == wx.WXK_ESCAPE:
            self.onButton_cancel(None)
        evt.Skip()

"""
==== Dev/Test code
"""
        
class MainFrame(wx.Frame):
    def __init__(self, parent, imgpaths, rows_page, lookahead, num_cols, cell_size, no_prefetch, numdigits, nprocs, statefile, *args, **kwargs):
        wx.Frame.__init__(self, parent, size=(1000, 700), *args, **kwargs)
        self.statefile = statefile
        self.mainpanel = TempMatchGrid(self)
        
        btn_activate = wx.Button(self, label="Activate Page...")
        btn_activate.Bind(wx.EVT_BUTTON, self.onButton_activate)
        
        btn_deactivate = wx.Button(self, label="Deactivate Page...")
        btn_deactivate.Bind(wx.EVT_BUTTON, self.onButton_deactivate)

        btn_pageup = wx.Button(self, label="Page Up")
        btn_pageup.Bind(wx.EVT_BUTTON, self.onButton_pageup)
        btn_pagedown = wx.Button(self, label="Page Down")
        btn_pagedown.Bind(wx.EVT_BUTTON, self.onButton_pagedown)
        
        btn_zoomin = wx.Button(self, label="Zoom In")
        btn_zoomin.Bind(wx.EVT_BUTTON, self.onButton_zoomin)
        btn_zoomout = wx.Button(self, label="Zoom Out")
        btn_zoomout.Bind(wx.EVT_BUTTON, self.onButton_zoomout)

        btn_layout = wx.Button(self, label="Layout")
        btn_layout.Bind(wx.EVT_BUTTON, lambda evt: self.mainpanel.Layout())
        btn_fit = wx.Button(self, label="Fit")
        btn_fit.Bind(wx.EVT_BUTTON, lambda evt: self.mainpanel.Fit())

        btn_sort = wx.Button(self, label="Sort Cells")
        btn_sort.Bind(wx.EVT_BUTTON, lambda evt: self.mainpanel.sort_cells())

        btn_sizer = wx.BoxSizer(wx.HORIZONTAL)
        btn_sizer.AddMany([(btn_activate,), (btn_deactivate,)])
        btn_sizer.AddMany([(btn_pageup,), (btn_pagedown,)])
        btn_sizer.AddMany([(btn_zoomin,), (btn_zoomout,)])
        btn_sizer.AddMany([((20,0),), (btn_layout,), (btn_fit,), ((20,0),), (btn_sort,)])
        
        btn_create = wx.Button(self, label="Create")
        btn_create.Bind(wx.EVT_BUTTON, lambda evt: self.mainpanel.set_mode(CREATE))
        btn_modify = wx.Button(self, label="Modify")
        btn_modify.Bind(wx.EVT_BUTTON, lambda evt: self.mainpanel.set_mode(IDLE))
        
        btnmode_sizer = wx.BoxSizer(wx.HORIZONTAL)
        btnmode_sizer.AddMany([(btn_create,), (btn_modify,)])

        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.sizer.Add(self.mainpanel, proportion=1, border=10, flag=wx.EXPAND | wx.ALL)
        self.sizer.Add(btn_sizer, flag=wx.ALIGN_CENTER)
        self.sizer.Add(btnmode_sizer, flag=wx.ALIGN_CENTER)
        self.SetSizer(self.sizer)
        self.Layout()
        
        self.mainpanel.set_object_limit(numdigits)
        self.mainpanel.NPROCS = nprocs
        if statefile and os.path.exists(statefile):
            print "(MainFrame) Using specified statefile:", statefile
            state = pickle.load(open(statefile, 'rb'))
            self.mainpanel.restore_state(state)
        else:
            self.mainpanel.start(imgpaths, rows_page=rows_page, lookahead=lookahead, num_cols=num_cols, cellsize=cell_size,
                                 DO_PREFETCH=not no_prefetch)

        self.Bind(wx.EVT_WINDOW_DESTROY, self.onDestroy)

    def onDestroy(self, evt):
        if self.statefile:
            print "(MainFrame) Saving state to statefile:", self.statefile
            pickle.dump(self.mainpanel.get_state(), open(self.statefile, 'wb'))
        evt.Skip()

    def onButton_activate(self, evt):
        dlg = wx.TextEntryDialog(self, message="Which page to activate?")
        status = dlg.ShowModal()
        if status != wx.ID_OK:
            return
        try:
            self.mainpanel.activate_page(int(dlg.GetValue()))
        except:
            traceback.print_exc()
            wx.MessageDialog(self, style=wx.OK, message="Invalid page entered!").ShowModal()
    def onButton_deactivate(self, evt):
        dlg = wx.TextEntryDialog(self, message="Which page to deactivate?")
        status = dlg.ShowModal()
        if status != wx.ID_OK:
            return
        try:
            self.mainpanel.deactivate_page(int(dlg.GetValue()))
        except:
            traceback.print_exc()
            wx.MessageDialog(self, style=wx.OK, message="Invalid page entered!").ShowModal()
    def onButton_pageup(self, evt):
        pass
    def onButton_pagedown(self, evt):
        pass
    def onButton_zoomin(self, evt):
        self.mainpanel.zoomin()
    def onButton_zoomout(self, evt):
        self.mainpanel.zoomout()

def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--imgsdir", help="Directory of images to \
display. Overrides the '--k' option.")

    parser.add_argument("--limit", type=int, 
                        help="Upper limit of images to process.")

    parser.add_argument("--rows_page", type=int, metavar="N", default=3,
                        help="Number of rows per page.")
    parser.add_argument("--lookahead", type=int, metavar="C", default=2,
                        help="Set the lookahead parameter.")
    parser.add_argument("--num_cols", type=int, metavar="COLS", default=4,
                        help="Set the number of columns.")
    parser.add_argument("--cellsize", type=int, nargs=2, metavar=("W", "H"), default=(200, 100),
                        help="Set the cell size.")

    parser.add_argument("--no_prefetch", action="store_true",
                        help="Don't a separate thread to pre-fetch images.")
    parser.add_argument("--numdigits", type=int,
                        help="Set the number of digits on each digitpatch.")
    parser.add_argument("--nprocs", type=int,
                        help="Number of processes to use for template matching.")

    parser.add_argument("--statefile",
                        help="Specify statefile to use.")
    return parser.parse_args()

def main():
    args = parse_args()
    print args.no_prefetch
    def load_imgpaths(imgsdir, limit):
        imgpaths = []
        for dirpath, dirnames, filenames in os.walk(imgsdir):
            for imgname in [f for f in filenames if f.lower().endswith(".png")]:
                if limit != None and len(imgpaths) >= limit:
                    return imgpaths
                imgpaths.append(os.path.join(dirpath, imgname))
        return imgpaths
    if args.imgsdir:
        imgpaths = load_imgpaths(args.imgsdir, args.limit)
    else:
        imgpaths = [None] * args.k

    app = wx.App(False)
    f = MainFrame(None, imgpaths, args.rows_page, args.lookahead, args.num_cols,
                  args.cellsize, args.no_prefetch, args.numdigits, args.nprocs,
                  args.statefile)
    f.Show()
    app.MainLoop()

if __name__ == '__main__':
    main()
