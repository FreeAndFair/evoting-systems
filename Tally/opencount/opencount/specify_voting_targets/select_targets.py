import sys, os, time, math, pdb, traceback, threading, Queue, copy, textwrap
import multiprocessing, csv
try:
    import cPickle as pickle
except ImportError:
    import pickle

from os.path import join as pathjoin

sys.path.append('..')

import wx, cv, numpy as np, Image, scipy, scipy.misc
from wx.lib.pubsub import Publisher
from wx.lib.scrolledpanel import ScrolledPanel

from panel_opencount import OpenCountPanel
import util_gui, util, graphcolour, config
import grouping.tempmatch as tempmatch
import labelcontest.group_contests as group_contests
import pixel_reg.shared as shared
import pixel_reg.imagesAlign as imagesAlign
import global_align.global_align as global_align

JOBID_TEMPMATCH_TARGETS = util.GaugeID("TemplateMatchTargets")

class SelectTargetsMainPanel(OpenCountPanel):
    GLOBALALIGN_JOBID = util.GaugeID("GlobalAlignJobId")

    def __init__(self, parent, *args, **kwargs):
        OpenCountPanel.__init__(self, parent, *args, **kwargs)

        self.proj = None

        _sanitycheck_callbacks = ((ID_FLAG_ONLYONE_TARGET,
                                   self._sanitycheck_handle_onlyone_target),
                                  (ID_FLAG_LONELY_TARGETS,
                                   self._sanitycheck_handle_lonelytargets),
                                  (ID_FLAG_CONTEST_ONE_TARGET,
                                   self._sanitycheck_handle_contest_one_target),
                                  (ID_FLAG_EMPTY_CONTESTS,
                                   self._sanitycheck_handle_empty_contest))
        for (id_flag, fn) in _sanitycheck_callbacks:
            self.add_sanity_check_callback(id_flag, fn)

        self.init_ui()

    def init_ui(self):
        self.seltargets_panel = SelectTargetsPanel(self)

        btn_getimgpath = wx.Button(self, label="Get Image Path...")
        btn_getimgpath.Bind(wx.EVT_BUTTON, self.onButton_getimgpath)

        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.sizer.Add(self.seltargets_panel, proportion=1, flag=wx.EXPAND)
        self.sizer.Add(btn_getimgpath)

        self.SetSizer(self.sizer)
        self.Layout()

    def start(self, proj, stateP, ocrtmpdir):
        self.proj = proj
        self.stateP = stateP
        
        # Maps group to reference image. Used if a different image
        # is needed to be used for alignment purposes.
        self.group_to_Iref = {}

        # GROUP2BALLOT: dict {int groupID: [int ballotID_i, ...]}
        group2ballot = pickle.load(open(pathjoin(proj.projdir_path,
                                                 proj.group_to_ballots), 'rb'))
        group_exmpls = pickle.load(open(pathjoin(proj.projdir_path,
                                                 proj.group_exmpls), 'rb'))
        b2imgs = pickle.load(open(proj.ballot_to_images, 'rb'))
        img2page = pickle.load(open(pathjoin(proj.projdir_path,
                                             proj.image_to_page), 'rb'))
        self.img2flip = pickle.load(open(pathjoin(proj.projdir_path,
                                                  proj.image_to_flip), 'rb'))
        # 0.) Munge GROUP2BALLOT to list of lists of lists
        groups = []
        numtasks = 0
        for groupID, ballotids in sorted(group_exmpls.iteritems(), key=lambda t: t[0]):
            group = []
            for ballotid in ballotids:
                if len(group) >= 5:
                    break
                imgpaths = b2imgs[ballotid]
                imgpaths_ordered = sorted(imgpaths, key=lambda imP: img2page[imP])
                group.append(imgpaths_ordered)
            numtasks += 1
            groups.append(group)
        self.displayed_imgpaths = groups

        self.proj.addCloseEvent(self.save_session)
        self.proj.addCloseEvent(self.seltargets_panel.save_session)
        align_outdir = pathjoin(proj.projdir_path, 'groupsAlign_seltargs')

        class GlobalAlignThread(threading.Thread):
            def __init__(self, groups, img2flip, align_outdir, ocrtmpdir, 
                         manager, queue, callback, jobid, tlisten, *args, **kwargs):
                threading.Thread.__init__(self, *args, **kwargs)
                self.groups = groups
                self.img2flip = img2flip
                self.align_outdir = align_outdir
                self.ocrtmpdir = ocrtmpdir
                self.manager = manager
                self.queue = queue
                self.callback = callback
                self.jobid = jobid
                self.tlisten = tlisten
            def run(self):
                print '...Globally-aligning a subset of each partition...'
                t = time.time()
                groups_align_map = do_align_partitions(self.groups, self.img2flip,
                                                       self.align_outdir, self.manager, self.queue,
                                                       N=None)
                dur = time.time() - t
                print '...Finished globally-aligning a subset of each partition ({0:.4f} s)'.format(dur)
                wx.CallAfter(Publisher().sendMessage, "signals.MyGauge.done", (self.jobid,))
                wx.CallAfter(self.callback, groups_align_map, self.ocrtmpdir)
                self.tlisten.stop()
        class ListenThread(threading.Thread):
            def __init__(self, queue, jobid, *args, **kwargs):
                threading.Thread.__init__(self, *args, **kwargs)
                self.queue = queue
                self.jobid = jobid
                self._stop = threading.Event()
            def stop(self):
                self._stop.set()
            def is_stopped(self):
                return self._stop.isSet()
            def run(self):
                while True:
                    if self.is_stopped():
                        return
                    try:
                        val = self.queue.get(block=True, timeout=1)
                        if val == True:
                            wx.CallAfter(Publisher().sendMessage, "signals.MyGauge.tick", (self.jobid,))
                    except Queue.Empty:
                        pass

        #if not os.path.exists(align_outdir):
        if not self.restore_session():
            manager = multiprocessing.Manager()
            queue = manager.Queue()
            if config.TIMER:
                config.TIMER.start_task("SelectTargets_GlobalAlign_CPU")
            tlisten = ListenThread(queue, self.GLOBALALIGN_JOBID)
            workthread = GlobalAlignThread(groups, self.img2flip, align_outdir, ocrtmpdir, 
                                           manager, queue, self.on_align_done, 
                                           self.GLOBALALIGN_JOBID, tlisten)
            workthread.start()
            tlisten.start()
            gauge = util.MyGauge(self, 1, thread=workthread, msg="Running Global Alignment...",
                                 job_id=self.GLOBALALIGN_JOBID)
            gauge.Show()
            wx.CallAfter(Publisher().sendMessage, "signals.MyGauge.nextjob", (numtasks, self.GLOBALALIGN_JOBID))
        else:
            # SelectTargets restores its self.partitions from stateP.
            seltargets_stateP = pathjoin(self.proj.projdir_path, '_state_selecttargets.p')
            self.seltargets_panel.start(None, self.img2flip, seltargets_stateP, ocrtmpdir)

    def on_align_done(self, groups_align_map, ocrtmpdir):
        if config.TIMER:
            config.TIMER.stop_task("SelectTargets_GlobalAlign_CPU")
        groups_align = []
        for groupid in sorted(groups_align_map.keys()):
            ballots = groups_align_map[groupid]
            groups_align.append(ballots)
        # Order the displayed groups by size (smallest to largest)
        groups_sizes = map(lambda g: -len(g), groups_align)
        groups_sizes_argsort = np.argsort(groups_sizes)
        groups_align_bysize = [groups_align[i] for i in groups_sizes_argsort]
        self.i2groupid = groups_sizes_argsort
        seltargets_stateP = pathjoin(self.proj.projdir_path, '_state_selecttargets.p')
        self.seltargets_panel.start(groups_align_bysize, self.img2flip, seltargets_stateP, ocrtmpdir)

    def stop(self):
        self.proj.removeCloseEvent(self.save_session)
        self.proj.removeCloseEvent(self.seltargets_panel.save_session)
        self.save_session()
        self.seltargets_panel.save_session()
        self.export_results()

    def restore_session(self):
        try:
            state = pickle.load(open(self.stateP, 'rb'))
            i2groupid = state['i2groupid']
            displayed_imgpaths = state['displayed_imgpaths']
            #self.group_to_Iref = state['group_to_Iref']
            self.i2groupid = i2groupid
            self.displayed_imgpaths = displayed_imgpaths
        except:
            return False
        return True

    def save_session(self):
        state = {'i2groupid': self.i2groupid,
                 'displayed_imgpaths': self.displayed_imgpaths,
                 #'group_to_Iref': self.group_to_Iref
                 }
        pickle.dump(state, open(self.stateP, 'wb'), pickle.HIGHEST_PROTOCOL)

    def export_results(self):
        """ For each group, export the locations of the voting
        targets to two locations:
            1.) A proj.target_locs pickle'd data structure
            2.) A dir of .csv files (for integration with LabelContests+
                InferContests).
            3.) A file 'target_roi' that SetThreshold/TargetExtraction will
                use when determining the target sort criterion.
            4.) A set of quarantined ballotids ('flagged' partitions)
        """
        try:
            os.makedirs(self.proj.target_locs_dir)
        except:
            pass
        pickle.dump(self.group_to_Iref, open(pathjoin(self.proj.projdir_path,'group_to_Iref.p'),'wb', pickle.HIGHEST_PROTOCOL))

        # Output the flagged groups at a ballotid-granularity
        groups_quar = sorted([self.i2groupid[idx] for idx in self.seltargets_panel.flagged_idxs])
        grp2bals = pickle.load(open(pathjoin(self.proj.projdir_path, 'group_to_ballots.p')))
        balids_quar = set()
        for grp_bad in groups_quar:
            balids = grp2bals[grp_bad]
            for balid in balids:
                balids_quar.add(balid)
        
        print "(SelectTargets) Quarantining {0} flagged groups ({1} ballots total)".format(len(groups_quar), len(balids_quar))
        pickle.dump(balids_quar, open(pathjoin(self.proj.projdir_path, 'quarantinedbals_seltargets.p'), 'wb'))
        # Also, temporarily export the quarantined groups.
        print "(SelectTargets) Exporting 'quarantinedgroups_seltarets.p' as well, just in case."
        pickle.dump(groups_quar, open(pathjoin(self.proj.projdir_path, 'quarantinedgroups_seltargets.p'), 'wb'))
        del grp2bals

        group_targets_map = {} # maps {int groupID: [csvpath_side0, ...]}
        # TARGET_LOCS_MAP: maps {int groupID: {int page: [CONTEST_i, ...]}}, where each
        #     CONTEST_i is: [contestbox, targetbox_i, ...], where each
        #     box := [x1, y1, width, height, id, contest_id]
        target_locs_map = {}
        lonely_targets_map = {} # maps {int i: {int side: [TargetBox_i, ...]}}
        fields = ('imgpath', 'id', 'x', 'y', 'width', 'height', 'label', 'is_contest', 'contest_id')
        imgsize = None # Assumes all voted ballots are the same dimensions
        for i, boxes_sides in self.seltargets_panel.boxes.iteritems():
            if i in self.seltargets_panel.flagged_idxs:
                continue
            group_idx = self.i2groupid[i]
            csvpaths = []
            for side, boxes in enumerate(boxes_sides):
                outpath = pathjoin(self.proj.target_locs_dir,
                                   "group_{0}_side_{1}.csv".format(group_idx, side))
                csvpaths.append(outpath)
                writer = csv.DictWriter(open(outpath, 'wb'), fields)
                # Make sure that TARGET_LOCS_MAP at least has something for this 
                # (To help out target extraction)
                target_locs_map.setdefault(group_idx, {}).setdefault(side, [])
                # BOX_ASSOCS: dict {int contest_id: [ContestBox, [TargetBox_i, ...]]}
                # LONELY_TARGETS: list [TargetBox_i, ...]
                box_assocs, lonely_targets = compute_box_ids(boxes)
                lonely_targets_map.setdefault(i, {}).setdefault(side, []).extend(lonely_targets)
                # For now, just grab one exemplar image from this group
                imgpath = self.seltargets_panel.partitions[i][0][side]
                if imgsize == None:
                    imgsize = cv.GetSize(cv.LoadImage(imgpath))
                rows_contests = []
                rows_targets = []
                id_c, id_t = 0, 0
                for contest_id, (contestbox, targetboxes) in box_assocs.iteritems():
                    x1_out, y1_out = contestbox.x1, contestbox.y1
                    w_out, h_out = contestbox.width, contestbox.height
                    # Make sure contest doesn't extend outside image.
                    x1_out = max(x1_out, 0)
                    y1_out = max(y1_out, 0)
                    if (x1_out + w_out) >= imgsize[0]:
                        w_out = imgsize[0] - x1_out - 1
                    if (y1_out + h_out) >= imgsize[1]:
                        h_out = imgsize[1] - y1_out - 1
                    rowC = {'imgpath': imgpath, 'id': id_c,
                            'x': x1_out, 'y': y1_out,
                            'width': w_out,
                            'height': h_out,
                            'label': '', 'is_contest': 1, 
                            'contest_id': contest_id}
                    rows_contests.append(rowC)
                    cbox = [x1_out, y1_out, w_out, h_out, id_c, contest_id]
                    curcontest = [] # list [contestbox, targetbox_i, ...]
                    curcontest.append(cbox)
                    id_c += 1
                    for box in targetboxes:
                        # Note: Ensure that all exported targets have the same dimensions,
                        # or risk breaking SetThreshold!
                        w, h = self.seltargets_panel.boxsize
                        x1_out, y1_out = box.x1, box.y1
                        # Don't let target extend outside the image
                        if (x1_out + w) >= imgsize[0]:
                            x1_out -= ((x1_out + w) - imgsize[0] + 1)
                        if (y1_out + h) >= imgsize[1]:
                            y1_out -= ((y1_out + h) - imgsize[1] + 1)
                        x1_out = max(x1_out, 0)
                        y1_out = max(y1_out, 0)
                        # Note: This doesn't necessarily guarantee that T
                        # is inside img bbox - however, since targets are
                        # small w.r.t image, this will always work.
                        rowT = {'imgpath': imgpath, 'id': id_t,
                               'x': x1_out, 'y': y1_out,
                               'width': w, 'height': h,
                               'label': '', 'is_contest': 0,
                               'contest_id': contest_id}
                        rows_targets.append(rowT)
                        tbox = [x1_out, y1_out, w, h, id_t, contest_id]
                        curcontest.append(tbox)
                        id_t += 1
                    target_locs_map.setdefault(group_idx, {}).setdefault(side, []).append(curcontest)
                writer.writerows(rows_contests + rows_targets)
            group_targets_map[group_idx] = csvpaths
        pickle.dump(group_targets_map, open(pathjoin(self.proj.projdir_path,
                                                     self.proj.group_targets_map), 'wb'),
                    pickle.HIGHEST_PROTOCOL)
        pickle.dump(target_locs_map, open(pathjoin(self.proj.projdir_path,
                                                   self.proj.target_locs_map), 'wb'),
                    pickle.HIGHEST_PROTOCOL)
        # target_roi := (int x1, y1, x2, y2). If self.target_roi is None, then
        # the string None will be written to the output file.
        # Otherwise, four comma-delimited ints will be written, like:
        #     40,40,100,100
        f_target_roi = open(pathjoin(self.proj.projdir_path, 'target_roi'), 'w')
        if self.seltargets_panel.target_roi:
            outstr = "{0},{1},{2},{3}".format(*self.seltargets_panel.target_roi)
        else:
            outstr = "None"
        print "(SelectTargets) Wrote '{0}' to: {1}".format(outstr, pathjoin(self.proj.projdir_path, 'target_roi'))
        print >>f_target_roi, outstr
        f_target_roi.close()
        # Warn User about lonely targets.
        # Note: This is currently handled in the UI during sanitychecks,
        #       but no harm in leaving this here too.
        _lst = []
        cnt = 0
        for i, targs_sidesMap in lonely_targets_map.iteritems():
            for side, targets in targs_sidesMap.iteritems():
                if targets:
                    print "...On Partition {0}, side {1}, there were {2} \
Lonely Targets - please check them out, or else they'll get ignored by \
LabelContests.".format(i, side, len(targets))
                    _lst.append("Partition={0} Side={1}".format(i, side))
                    cnt += len(targets)
        if _lst:
            dlg = wx.MessageDialog(self, message="Warning - there were {0} \
targets that were not enclosed in a contest. Please check them out, otherwise \
they'll get ignored by LabelContests. They are: {1}".format(cnt, str(_lst)),
                                   style=wx.OK)
            dlg.ShowModal()

    def invoke_sanity_checks(self, *args, **kwargs):
        """ Code that actually calls each sanity-check with application
        specific arguments. Outputs a list of statuses.
        """
        lst_statuses = check_all_images_have_targets(self.seltargets_panel.boxes, self.seltargets_panel.flagged_idxs)
        #lst_statuses = check_all_images_have_targets(self.seltargets_panel.boxes, set())
        return lst_statuses

    def onButton_getimgpath(self, evt):
        S = self.seltargets_panel
        cur_groupid = self.i2groupid[S.cur_i]
        imgpath = self.displayed_imgpaths[cur_groupid][S.cur_j][S.cur_page]
        dlg = wx.MessageDialog(self, message="Displayed Imagepath: {0}".format(imgpath),
                               style=wx.OK)
        dlg.ShowModal()

    """ 
    ===============================================
    ==== SanityCheck callback handling methods ====
    ===============================================
    """

    def rails_show_images(self, grps, grps_data=None,
                          btn_labels=("Stop Here", "Next Image"), 
                          btn_fns=(lambda i, grps, grps_data: False,
                                   lambda i, grps, grps_data: 'next'),
                          retval_end=False,
                          title_fn=lambda i, grps, grps_data: "Generic Dialog Title",
                          msg_fn=lambda i, grps, grps_data: "Generic Description"):
        """ A simple framework that takes control of the UI, and directs
        the user to the images indicated by BTN_LABELS. In other words,
        this is a 'rail-guided' UI flow.
        Input:
            list GRPS: [(int grp_idx, int side), ...]
            dict GRPS_DATA: {(int grp_idx, int side): obj DATA}
                (Optional) Allows you to pass additional data associated
                with each (grp_idx, side) to relevant btn_fns or dialog
                message fns.
            tuple BTN_LABELS: (str LABEL_0, ..., str LABEL_N)
                At each image in GRPS, a dialog window with N buttons
                will be displayed to the user. You can control what each
                button says via this argument.
            tuple BTN_FNS: (func FN_0, ..., func FN_N)
                The function to invoke when the user clicks button N
                after image i is shown. Each function accepts to 
                arguments: int i          - the index we are at in GRPS
                           lst grps       - the input GRPS.
                           dict grps_data - data for each group GRP.
                It should return one of three outputs:
                    bool True: 
                        Stop the rail-guided tour, and signal that the
                        user /can/ move on
                    bool False: 
                        Stop the rail-guided tour, and signal that the 
                        user /can't/ move on
                    tuple 'next':
                        Display the next image.
            bool retval_end: 
                Value to return if the user reaches the end of the list
                of images. True if the user can move on, False o.w.
            func TITLE_FN: 
            func MSG_FN:
        """
        grps_data = grps_data if grps_data != None else {}
        panel = self.seltargets_panel
        btn_ids = range(len(btn_labels))
        for i, (grp_idx, side) in enumerate(grps):
            panel.txt_totalballots.SetLabel(str(len(panel.partitions[grp_idx])))
            panel.txt_totalpages.SetLabel(str(len(panel.partitions[grp_idx][0])))
            panel.display_image(grp_idx, 0, side)
            dlg_title = title_fn(i, grps, grps_data)
            dlg_msg = msg_fn(i, grps, grps_data)
            status = util.WarningDialog(self, dlg_msg,
                                        btn_labels,
                                        btn_ids,
                                        title=dlg_title).ShowModal()
            btn_fn = btn_fns[status]
            result = btn_fn(i, grps, grps_data)
            if result == True:
                return True
            elif result == False:
                return False
        return retval_end

    def _sanitycheck_handle_onlyone_target(self, grps):
        """ Guides the user to each image that only has one voting target.
        Input:
            list GRPS: [(int grp_idx, int side), ...]
        Output:
            True if the user can move on, False o.w.
        """
        fn_stop = lambda i, grps, grps_data: False
        fn_nextimg = lambda i, grps, grps_data: 'next'
        fn_skip = lambda i, grps, grps_data: True
        btn_labels = ("I can fix this.", "Next Image", "Everything is Fine")
        btn_fns = (fn_stop, fn_nextimg, fn_skip)
        dlg_titlefn = lambda i,grps,grps_data: "OpenCount Warning: Only one voting target"
        dlg_msgfn = lambda i,grps, grps_data: "This is an image with only \
one voting target.\n\
Image {0} out of {1}".format(i+1, len(grps))
        return self.rails_show_images(grps, btn_labels=btn_labels,
                                      btn_fns=btn_fns,
                                      retval_end=True,
                                      title_fn=dlg_titlefn,
                                      msg_fn=dlg_msgfn)
    
    def _sanitycheck_handle_lonelytargets(self, lonely_targets_map):
        """ Guide the user to each image that has a voting target(s) not
        enclosed within a contest.
        Input:
            dict LONELY_TARGETS_MAP: {(int grp_idx, int side): [TargetBox_i, ...]}
        Output:
            False (this is a fatal error.)
        """
        def make_dlg_msg(i, grps, grps_data):
            msgbase = "This is an image with {0} voting targets that are \
not enclosed within a contest."
            stats = "Image {0} out of {1}."
            return msgbase.format(len(grps_data[grps[i]])) + "\n" + stats.format(i+1, total_imgs)

        total_imgs = len(lonely_targets_map)
        total_targets = sum(map(len, lonely_targets_map.values()))
        # Sort GRPS by first grpidx, then by side
        grps = sorted(lonely_targets_map.keys(), key=lambda t: t[0]+t[1])
        return self.rails_show_images(grps, grps_data=lonely_targets_map,
                                      retval_end=False,
                                      btn_labels=("I can fix this.", "Next Image"),
                                      btn_fns=(lambda i,grps,grpdata: False,
                                               lambda i,grps,grpdata: 'next'),
                                      title_fn=lambda i,grps,grpdata: "OpenCount Fatal Warning: Lonely Targets",
                                      msg_fn=make_dlg_msg)

    def _sanitycheck_handle_contest_one_target(self, contests_one_target):
        """ Guides the user to each offending image.
        Input:
            dict CONTESTS_ONE_TARGET: {(int grp_idx, int side): [ContestBox_i, ...]}
        Output:
            False (this is a fatal error).
        """
        # TODO: Refactor to use self.rails_show_images
        panel = self.seltargets_panel
        total_imgs = len(contests_one_target)
        total_contests = sum(map(len, contests_one_target.values()))
        _title = "OpenCount Fatal Warning: Bad Contests Detected"
        _msgbase = "This is an image with {0} contests that only have \
one voting target."
        _msgfooter = "Image {0} out of {1}"
        ID_RESUME = 0
        ID_NEXT_IMAGE = 1
        for i, ((grp_idx, side), contestboxes) in enumerate(contests_one_target.iteritems()):
            panel.txt_totalballots.SetLabel(str(len(panel.partitions[grp_idx])))
            panel.txt_totalpages.SetLabel(str(len(panel.partitions[grp_idx][0])))
            panel.display_image(grp_idx, 0, side)
            msgout = _msgbase.format(len(contestboxes)) + "\n" + _msgfooter.format(i+1, total_imgs)
            status = util.WarningDialog(self, msgout, ("I can fix this.", "Next Image"),
                                        (ID_RESUME, ID_NEXT_IMAGE), title=_title).ShowModal()
            if status == ID_RESUME:
                return False
        return False
    def _sanitycheck_handle_empty_contest(self, empty_contests):
        """ Guides the user to each empty contest box.
        Input:
            dict EMPTY_CONTESTS: {(int grp_idx, int side): [ContestBox_i, ...]
        Output:
            False (this is a fatal error).
        """
        # TODO: Refactor to use self.rails_show_images
        panel = self.seltargets_panel
        total_imgs = len(empty_contests)
        _title = "OpenCount Fatal Warning: Empty Contests Detected"
        _msgbase = "This is an image with {0} contests that have no \
voting targets enclosed."
        _msgfooter = "Image {0} out of {1}"
        ID_RESUME = 0
        ID_NEXT_IMAGE = 1
        ID_SKIPALL = 2
        for i, ((grp_idx, side), contestboxes) in enumerate(empty_contests.iteritems()):
            panel.txt_totalballots.SetLabel(str(len(panel.partitions[grp_idx])))
            panel.txt_totalpages.SetLabel(str(len(panel.partitions[grp_idx][0])))
            panel.display_image(grp_idx, 0, side)
            msgout = _msgbase.format(len(contestboxes)) + "\n" + _msgfooter.format(i+1, total_imgs)
            status = util.WarningDialog(self, msgout, ("I can fix this.", "Next Image", "- Ignore the empty contests -"),
                                        (ID_RESUME, ID_NEXT_IMAGE, ID_SKIPALL), title=_title).ShowModal()
            if status == ID_RESUME:
                return False
            elif status == ID_SKIPALL:
                return True
        # TODO: Temp. make this a non-fatal error
        return True

class SelectTargetsPanel(ScrolledPanel):
    """ A widget that allows you to find voting targets on N ballot
    partitions
    """
    
    # TM_MODE_ALL: Run template matching on all images
    TM_MODE_ALL = 901
    # TM_MODE_POST: Run template matching only on images after (post) the
    #               currently-displayed group.
    TM_MODE_POST = 902

    def __init__(self, parent, *args, **kwargs):
        ScrolledPanel.__init__(self, parent, *args, **kwargs)
        self.parent = parent

        # self.partitions: [[[imgpath_i0front, ...], ...], [[imgpath_i1front, ...], ...], ...]
        self.partitions = None
        # self.inv_map: {str imgpath: (int i, int j, int page)}
        self.inv_map = None
        # self.cur_i: Index of currently-displayed partition
        self.cur_i = None
        # self.cur_j: Index of currently-displayed image within partition CUR_I.
        self.cur_j = None
        # self.cur_page: Currently-displayed page
        self.cur_page = None

        # self.boxes: {int i: [[Box_iFront, ...], ...]}
        self.boxes = {}

        # BOXSIZE: (int w, int h), used to enforce that all voting targets
        # are the same size.
        self.boxsize = None

        # Sensitivity for Template Matching
        self.tm_param = 0.93
        # Window sizes for Smoothing
        self.win_ballot = (13, 13)
        self.win_target = (15, 15)
        self.tm_mode = self.TM_MODE_POST

        # STATEP: Path for state file.
        self.stateP = None

        # tuple TARGET_ROI: (int x1, y1, x2, y2). Is set when the user
        # draws their first target box.
        self.target_roi = None

        # set FLAGGED_IDXS: set([int i0, int i1, ...])
        #     Stores any flagged 'partitions'.
        self.flagged_idxs = None

        self.toolbar = Toolbar(self)
        self.imagepanel = TargetFindPanel(self, self.do_tempmatch)

        txt = wx.StaticText(self, label="Draw a rectangle around each \
voting target on this ballot.")

        btn_next = wx.Button(self, label="Next Image...")
        btn_next.Bind(wx.EVT_BUTTON, self.onButton_nextimage)
        btn_prev = wx.Button(self, label="Prev Image...")
        btn_prev.Bind(wx.EVT_BUTTON, self.onButton_previmage)
        sizer_btnmove = wx.BoxSizer(wx.VERTICAL)
        sizer_btnmove.AddMany([(btn_next,), (btn_prev,)])

        btn_nextpartition = wx.Button(self, label="Next Style...")
        btn_prevpartition = wx.Button(self, label="Previous Style...")
        sizer_partitionbtns = wx.BoxSizer(wx.VERTICAL)
        sizer_partitionbtns.AddMany([(btn_nextpartition,), (btn_prevpartition,)])

        btn_nextimg = wx.Button(self, label="Next Ballot")
        btn_previmg = wx.Button(self, label="Previous Ballot")
        sizer_ballotbtns = wx.BoxSizer(wx.VERTICAL)
        sizer_ballotbtns.AddMany([(btn_nextimg,), (btn_previmg,)])

        btn_nextpage = wx.Button(self, label="Next Page")
        btn_prevpage = wx.Button(self, label="Previous Page")
        sizer_pagebtns = wx.BoxSizer(wx.VERTICAL)
        sizer_pagebtns.AddMany([(btn_nextpage,), (btn_prevpage,)])
        
        btn_nextpartition.Bind(wx.EVT_BUTTON, self.onButton_nextpartition)
        btn_prevpartition.Bind(wx.EVT_BUTTON, self.onButton_prevpartition)
        btn_nextimg.Bind(wx.EVT_BUTTON, self.onButton_nextimg)
        btn_previmg.Bind(wx.EVT_BUTTON, self.onButton_previmg)
        btn_nextpage.Bind(wx.EVT_BUTTON, self.onButton_nextpage)
        btn_prevpage.Bind(wx.EVT_BUTTON, self.onButton_prevpage)

        sizer_jump_stylebal = wx.BoxSizer(wx.VERTICAL)

        btn_jump_partition = wx.Button(self, label="Jump to Style...")
        btn_jump_ballot = wx.Button(self, label="Jump to Ballot...")
        sizer_jump_stylebal.AddMany([(btn_jump_partition,), (btn_jump_ballot,)])
        
        btn_jump_error = wx.Button(self, label="Next Error...")
        btn_selectIref = wx.Button(self, label="Select as reference image.")
        btn_selectIref.Bind(wx.EVT_BUTTON, self.onButton_selectIref)
        btn_flag_partition = wx.Button(self, label="Quarantine this Style")
        btn_flag_partition.Bind(wx.EVT_BUTTON, self.onButton_flagpartition)

        sizer_btn_jump = wx.BoxSizer(wx.HORIZONTAL)
        #sizer_btn_jump.Add(btn_jump_partition, border=10, flag=wx.ALL)
        #sizer_btn_jump.Add(btn_jump_ballot, border=10, flag=wx.ALL)
        sizer_btn_jump.Add(btn_jump_error, border=10, flag=wx.ALL)
        sizer_btn_jump.Add(btn_selectIref, border=10, flag=wx.ALL)
        sizer_btn_jump.Add(btn_flag_partition, border=10, flag=wx.ALL)
        btn_jump_partition.Bind(wx.EVT_BUTTON, self.onButton_jump_partition)
        btn_jump_ballot.Bind(wx.EVT_BUTTON, self.onButton_jump_ballot)
        btn_jump_error.Bind(wx.EVT_BUTTON, self.onButton_jump_error)
        
        btn_sizer = wx.BoxSizer(wx.HORIZONTAL)
        btn_sizer.Add(sizer_btnmove, border=10, flag=wx.ALL)
        btn_sizer.Add(sizer_partitionbtns, border=10, flag=wx.ALL)
        btn_sizer.Add((80,0))
        btn_sizer.Add(sizer_ballotbtns, border=10, flag=wx.ALL)
        btn_sizer.Add(sizer_pagebtns, border=10, flag=wx.ALL)
        btn_sizer.Add(sizer_jump_stylebal, border=10, flag=wx.ALL)
        btn_sizer.Add((60,0))
        btn_sizer.Add(sizer_btn_jump, border=10, flag=wx.ALL)

        txt1 = wx.StaticText(self, label="Style: ")
        self.txt_curpartition = wx.StaticText(self, label="1")
        txt_slash0 = wx.StaticText(self, label=" / ")
        self.txt_totalpartitions = wx.StaticText(self, label="Foo")
        
        txt2 = wx.StaticText(self, label="Ballot (subset of full): ")
        self.txt_curballot = wx.StaticText(self, label="1")
        txt_slash1 = wx.StaticText(self, label=" / ")
        self.txt_totalballots = wx.StaticText(self, label="Bar")
        
        txt3 = wx.StaticText(self, label="Page: ")
        self.txt_curpage = wx.StaticText(self, label="1")
        txt_slash2 = wx.StaticText(self, label=" / ")
        self.txt_totalpages = wx.StaticText(self, label="Baz")
        self.txt_curimgpath = wx.StaticText(self, label="")
        self.txt_sizer = wx.BoxSizer(wx.HORIZONTAL)
        self.txt_sizer.AddMany([(txt1,),
                                (self.txt_curpartition,), (txt_slash0,), (self.txt_totalpartitions,),
                                (50,0), (txt2,),
                                (self.txt_curballot,), (txt_slash1,), (self.txt_totalballots,),
                                (50,0), (txt3,),
                                (self.txt_curpage,), (txt_slash2,), (self.txt_totalpages,),
                                (50,0), (self.txt_curimgpath)])

        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.sizer.Add(txt, flag=wx.ALIGN_CENTER)
        self.sizer.Add(self.toolbar, flag=wx.EXPAND)
        self.sizer.Add(self.imagepanel, proportion=1, flag=wx.EXPAND)
        self.sizer.Add(btn_sizer, flag=wx.ALIGN_CENTER)
        self.sizer.Add(self.txt_sizer)

        self.SetSizer(self.sizer)

    def start(self, partitions, img2flip, stateP, ocrtempdir):
        """
        Input:
            list PARTITIONS: A list of lists of lists, encoding partition+ballot+side(s):
                [[[imgpath_i0_front, ...], ...], [[imgpath_i1_front, ...], ...], ...]
            dict IMG2FLIP: maps {str imgpath: bool isflipped}
            str STATEP: Path of the statefile.
            str OCRTEMPDIR: Used for InferContestRegion.
        """
        self.img2flip = img2flip
        self.stateP = stateP
        self.ocrtempdir = ocrtempdir
        if not self.restore_session():
            # 0.) Populate my self.INV_MAP
            self.partitions = partitions
            self.inv_map = {}
            self.boxes = {}
            self.boxsize = None
            self.flagged_idxs = set()
            for i, imgpaths in enumerate(self.partitions):
                for j, ballot in enumerate(imgpaths):
                    for page, imgpath in enumerate(ballot):
                        self.inv_map[imgpath] = i, j, page
                # (allows for variable-num pages)
                self.boxes[i] = [[] for _ in xrange(len(ballot))]
        # 1.) Update any StaticTexts in the UI.
        self.txt_totalpartitions.SetLabel(str(len(self.partitions)))
        self.txt_totalballots.SetLabel(str(len(self.partitions[0])))
        self.txt_totalpages.SetLabel(str(len(self.partitions[0][0])))
        self.txt_sizer.Layout()
        self.display_image(0, 0, 0, autofit=True)

        # 2.) Start in Target-Create mode.
        self.imagepanel.set_mode_m(BoxDrawPanel.M_CREATE)
        self.imagepanel.boxtype = TargetBox

    def restore_session(self):
        try:
            state = pickle.load(open(self.stateP, 'rb'))
            inv_map = state['inv_map']
            boxes = state['boxes']
            boxsize = state['boxsize']
            partitions = state['partitions']
            target_roi = state.get('target_roi', None) # Handle legacy statefiles
            flagged_idxs = state.get('flagged_idxs', set()) # Legacy
            self.inv_map = inv_map
            self.boxes = boxes
            self.boxsize = boxsize
            self.partitions = partitions
            self.target_roi = target_roi
            self.flagged_idxs = flagged_idxs
        except:
            return False
        return True
            
    def save_session(self):
        state = {'inv_map': self.inv_map,
                 'boxes': self.boxes,
                 'boxsize': self.boxsize,
                 'partitions': self.partitions,
                 'target_roi': self.target_roi,
                 'flagged_idxs': self.flagged_idxs}
        pickle.dump(state, open(self.stateP, 'wb'), pickle.HIGHEST_PROTOCOL)

    def do_tempmatch(self, box, img, patch=None):
        """ Runs template matching on all images within the current
        partition, using the BOX from IMG as the template.
        Input:
            Box BOX:
            PIL IMG:
            PIL PATCH:
                If given, then this PATCH directly as the template image,
                rather than using BOX to extract a patch from IMG. This
                will skip the auto-cropping.
        """
        self.Disable()
        if config.TIMER:
            config.TIMER.start_task("SelectTargets_TempMatch_CPU")
        if patch == None:
            # 1.) Do an autofit.
            patch_prefit = img.crop((box.x1, box.y1, box.x2, box.y2))
            patch = util_gui.fit_image(patch_prefit, padx=2, pady=2)
        patch_cv = pil2iplimage(patch)
        # 2.) Apply a smooth on PATCH (first adding a white border, to
        # avoid the smooth darkening PATCH, but brightening IMG).
        BRD = 20    # Amt. of white border
        patchB = cv.CreateImage((patch_cv.width+BRD, patch_cv.height+BRD), patch_cv.depth, patch_cv.channels)
        # Pass '0' as bordertype due to undocumented OpenCV flag IPL_BORDER_CONSTANT
        # being 0. Wow!
        cv.CopyMakeBorder(patch_cv, patchB, (BRD/2, BRD/2), 0, 255)
        xwin, ywin = self.win_target
        cv.Smooth(patchB, patchB, cv.CV_GAUSSIAN, param1=xwin, param2=ywin)
        # 2.a.) Copy the smooth'd PATCHB back into PATCH
        #patch_cv = cv.GetSubRect(patchB, (BRD/2, BRD/2, patch_cv.width, patch_cv.height))
        cv.SetImageROI(patchB, (BRD/2, BRD/2, patch_cv.width, patch_cv.height))
        patch = patchB
        #patch = iplimage2pil(patchB)
        #patch.save("_patch.png")        
        cv.SaveImage("_patch.png", patch)
        # 3.) Run template matching across all images in self.IMGPATHS,
        # using PATCH as the template.
        if self.tm_mode == self.TM_MODE_ALL:
            # Template match on /all/ images across all partitions, all pages
            imgpaths = sum([t for t in sum(self.partitions, [])], [])
        elif self.tm_mode == self.TM_MODE_POST:
            # Template match only on images after this partition (including 
            # this partition)
            imgpaths = sum([t for t in sum(self.partitions[self.cur_i:], [])], [])
            imgpaths = imgpaths[self.cur_page:] # Don't run on prior pages
        print "...Running template matching on {0} images...".format(len(imgpaths))
        queue = Queue.Queue()
        thread = TM_Thread(queue, JOBID_TEMPMATCH_TARGETS, patch, img,
                           imgpaths, self.tm_param, self.win_ballot, self.win_target,
                           self.on_tempmatch_done)
        thread.start()

        gauge = util.MyGauge(self, 1, job_id=JOBID_TEMPMATCH_TARGETS,
                             msg="Finding Voting Targets...")
        gauge.Show()
        num_tasks = len(imgpaths)
        Publisher().sendMessage("signals.MyGauge.nextjob", (num_tasks, JOBID_TEMPMATCH_TARGETS))

    def on_tempmatch_done(self, results, w, h):
        """ Invoked after template matching computation is complete. 
        Input:
            dict RESULTS: maps {str imgpath: [(x1,y1,x2,y2,score_i), ...}. The matches
                that template matching discovered.
            int w: width of the patch
            int h: height of the patch
        """
        def is_overlap(rect1, rect2):
            def is_within_box(pt, box):
                return box.x1 < pt[0] < box.x2 and box.y1 < pt[1] < box.y2
            x1, y1, x2, y2 = rect1.x1, rect1.y1, rect1.x2, rect1.y2
            w, h = abs(x2-x1), abs(y2-y1)
            # Checks (in order): UL, UR, LR, LL corners
            return (is_within_box((x1,y1), rect2) or
                    is_within_box((x1+w,y1), rect2) or 
                    is_within_box((x1+w,y1+h), rect2) or 
                    is_within_box((x1,y1+h), rect2))
        def too_close(b1, b2):
            w, h = abs(b1.x1-b1.x2), abs(b1.y1-b1.y2)
            return ((abs(b1.x1 - b2.x1) <= w / 2.0 and
                     abs(b1.y1 - b2.y1) <= h / 2.0) or
                    is_overlap(b1, b2) or 
                    is_overlap(b2, b1))
        if config.TIMER:
            config.TIMER.stop_task("SelectTargets_TempMatch_CPU")
        # 1.) Add the new matches to self.BOXES, but also filter out
        # any matches in RESULTS that are too close to previously-found
        # matches.
        _cnt_added = 0
        # Sort by the 'j' index, e.g. prefer matches from the main-displayed
        # image first.
        for imgpath, matches in sorted(results.iteritems(), key=lambda (imP, mats): self.inv_map[imP][1]):
            partition_idx, j, page = self.inv_map[imgpath]
            for (x1, y1, x2, y2, score) in matches:
                boxB = TargetBox(x1, y1, x1+w, y1+h)
                # 1.a.) See if any already-existing TargetBox is too close
                do_add = True
                for boxA in [b for b in self.boxes[partition_idx][page] if isinstance(b, TargetBox)]:
                    if too_close(boxA, boxB):
                        do_add = False
                        break
                if do_add:
                    # 1.b.) Enforce constraint that all voting targets
                    #       are the same size.
                    if self.boxsize == None:
                        self.boxsize = (w, h)
                    else:
                        boxB.x2 = boxB.x1 + self.boxsize[0]
                        boxB.y2 = boxB.y1 + self.boxsize[1]
                    self.boxes.setdefault(partition_idx, [])[page].append(boxB)
                    _cnt_added += 1
        print 'Added {0} new boxes from this tempmatch run.'.format(_cnt_added)
        print 'Num boxes in current partition:', len(self.boxes[self.cur_i][self.cur_page])
        self.imagepanel.set_boxes(self.boxes[self.cur_i][self.cur_page])
        self.Refresh()
        self.Enable()
        print "...Finished adding results from tempmatch run."

    def display_image(self, i, j, page, autofit=False):
        """ Displays the J-th image in partition I. Also handles
        reading/saving in the currently-created boxes for the old/new image.
        If AUTOFIT is True, then this will auto-scale the image such that
        if fits entirely in the current client size.
        Input:
            int I: Which partition to display
            int J: Which image in partition I to display.
            int PAGE: Which page to display.
        Output:
            Returns the (I,J,PAGE) we decided to display, if successful.
        """
        if i < 0 or i >= len(self.partitions):
            print "Invalid partition idx:", i
            pdb.set_trace()
        elif j < 0 or j >= len(self.partitions[i]):
            print "Invalid image idx {0} into partition {1}".format(j, i)
            pdb.set_trace()
        # 0.) Save boxes of old image
        '''
        if self.cur_i != None:
            self.boxes.setdefault(self.cur_i, []).extend(self.imagepanel.boxes)
        '''
        self.cur_i, self.cur_j, self.cur_page = i, j, page
        imgpath = self.partitions[i][j][page]
        
        # 1.) Display New Image
        wximg = wx.Image(imgpath, wx.BITMAP_TYPE_ANY)
        if autofit:
            wP, hP = self.imagepanel.GetClientSize()
            w_img, h_img = wximg.GetWidth(), wximg.GetHeight()
            if w_img > h_img and w_img > wP:
                _c = w_img / float(wP)
                w_img_new = wP
                h_img_new = int(round(h_img / _c))
            elif w_img < h_img and h_img > hP:
                _c = h_img / float(hP)
                w_img_new = int(round(w_img / _c))
                h_img_new = hP
            else:
                w_img_new, h_img_new = w_img, h_img
            self.imagepanel.set_image(wximg, size=(w_img_new, h_img_new))
        else:
            self.imagepanel.set_image(wximg)
        
        # 2.) Read in previously-created boxes for I (if exists)
        boxes = self.boxes.get(self.cur_i, [])[page]
        self.imagepanel.set_boxes(boxes)

        #self.SetupScrolling()
        # 3.) Finally, update relevant StaticText in the UI.
        self.txt_curimgpath.SetLabel(imgpath)
        self.txt_curpartition.SetLabel(str(self.cur_i+1))
        self.txt_curballot.SetLabel(str(self.cur_j+1))
        self.txt_curpage.SetLabel(str(self.cur_page+1))
        self.txt_sizer.Layout()
        self.Refresh()

        if self.cur_i in self.flagged_idxs:
            print "(SelectTargets) Idx {0} was flagged by user!".format(self.cur_i)
            dlg = wx.MessageDialog(self, style=wx.OK,
                                   message="This 'partition' was flagged by the user.")
            dlg.ShowModal()

        return (self.cur_i,self.cur_j,self.cur_page)

    def resize_targets(self, x1_del, y1_del, x2_del, y2_del):
        """ Resizes all voting targets by shifting each corner by input
        X1_DEL, Y1_DEL, X2_DEL, Y2_DEL.
        """
        if not self.boxsize:
            print "Can't call resize_targets() when no targets exist."
            return
        w_new = self.boxsize[0] - x1_del + x2_del
        h_new = self.boxsize[1] - y1_del + y2_del
        if w_new <= 1 or h_new <= 1:
            print "New dimensions are degenerate: w,h=({0},{1})".format(w_new, h_new)
            return
        self.boxsize = w_new, h_new
        for partition_idx, pages_tpl in self.boxes.iteritems():
            for page, boxes in enumerate(pages_tpl):
                for target in [b for b in boxes if isinstance(b, TargetBox)]:
                    target.x1 += x1_del
                    target.y1 += y1_del
                    target.x2 += x2_del
                    target.y2 += y2_del
        self.imagepanel.dirty_all_boxes()
        self.Refresh()

    def display_nextpartition(self):
        next_idx = self.cur_i + 1
        if next_idx >= len(self.partitions):
            return None
        self.txt_totalballots.SetLabel(str(len(self.partitions[next_idx])))
        self.txt_totalpages.SetLabel(str(len(self.partitions[next_idx][0])))
        return self.display_image(next_idx, 0, 0)
    def display_prevpartition(self):
        prev_idx = self.cur_i - 1
        if prev_idx < 0:
            return None
        self.txt_totalballots.SetLabel(str(len(self.partitions[prev_idx])))
        self.txt_totalpages.SetLabel(str(len(self.partitions[prev_idx][0])))
        return self.display_image(prev_idx, 0, 0)

    def display_nextimg(self):
        """ Displays the next image in the current partition. If the end
        of the list is reached, returns None, and does nothing. Else, 
        returns the new image index.
        """
        next_idx = self.cur_j + 1
        if next_idx >= len(self.partitions[self.cur_i]):
            return None
        self.txt_totalpages.SetLabel(str(len(self.partitions[self.cur_i][next_idx])))
        return self.display_image(self.cur_i, next_idx, self.cur_page)
    def display_previmg(self):
        prev_idx = self.cur_j - 1
        if prev_idx < 0:
            return None
        self.txt_totalpages.SetLabel(str(len(self.partitions[self.cur_i][prev_idx])))
        return self.display_image(self.cur_i, prev_idx, self.cur_page)
    def display_nextpage(self):
        next_idx = self.cur_page + 1
        if next_idx >= len(self.partitions[self.cur_i][self.cur_j]):
            return None
        return self.display_image(self.cur_i, self.cur_j, next_idx)
    def display_prevpage(self):
        prev_idx = self.cur_page - 1
        if prev_idx < 0:
            return None
        return self.display_image(self.cur_i, self.cur_j, prev_idx)
    def onButton_nextimage(self, evt):
        """ Take the user to the next page or partition. """
        if self.display_nextpage() == None:
            self.display_nextpartition()
    def onButton_previmage(self, evt):
        """ Take the user to the previous page or partition. """
        if self.display_prevpage() == None:
            prev_i = self.cur_i - 1
            if prev_i < 0:
                return
            if not self.partitions[prev_i]:
                print "(Error) There appears to be an empty partition at i={0}".format(prev_i)
                return
            numpages = len(self.partitions[prev_i][0])
            self.display_image(prev_i, 0, numpages - 1)
            
    def onButton_nextpartition(self, evt):
        self.display_nextpartition()
    def onButton_prevpartition(self, evt):
        self.display_prevpartition()
    def onButton_nextimg(self, evt):
        self.display_nextimg()
    def onButton_previmg(self, evt):
        self.display_previmg()
    def onButton_nextpage(self, evt):
        self.display_nextpage()
    def onButton_prevpage(self, evt):
        self.display_prevpage()
    def onButton_flagpartition(self, evt):
        print "(SelectTargets) Flagging partition '{0}' as quarantined.".format(self.cur_i)
        self.flagged_idxs.add(self.cur_i)

    def zoomin(self, amt=0.1):
        self.imagepanel.zoomin(amt=amt)
    def zoomout(self, amt=0.1):
        self.imagepanel.zoomout(amt=amt)

    def onButton_jump_partition(self, evt):
        dlg = wx.TextEntryDialog(self, "Which Group Number?", "Enter group number")
        status = dlg.ShowModal()
        if status == wx.ID_CANCEL:
            return
        try:
            idx = int(dlg.GetValue()) - 1
        except:
            print "Invalid index:", idx
            return
        if idx < 0 or idx >= len(self.partitions):
            print "Invalid group index:", idx
            return
        self.txt_totalballots.SetLabel(str(len(self.partitions[idx])))
        self.txt_totalpages.SetLabel(str(len(self.partitions[idx][0])))
        self.display_image(idx, 0, 0)

    def onButton_jump_ballot(self, evt):
        dlg = wx.TextEntryDialog(self, "Which Ballot Number?", "Enter Ballot number")
        status = dlg.ShowModal()
        if status == wx.ID_CANCEL:
            return
        try:
            idx = int(dlg.GetValue()) - 1
        except:
            print "Invalid index:", idx
            return
        if idx < 0 or idx >= len(self.partitions[self.cur_i]):
            print "Invalid ballot index:", idx
            return
        self.txt_totalpages.SetLabel(str(len(self.partitions[self.cur_i][idx])))
        self.display_image(self.cur_i, idx, 0)

    def onButton_jump_error(self, evt):
        if 'next_errors' in dir(self) and self.next_errors != []:
            idx,v = self.next_errors.pop()
            self.txt_totalballots.SetLabel(str(len(self.partitions[idx])))
            self.txt_totalpages.SetLabel(str(len(self.partitions[idx][0])))
            self.display_image(idx, 0, v)

    def onButton_selectIref(self, evt):
        print self.cur_j
        S = self.parent.seltargets_panel
        cur_groupid = self.parent.i2groupid[S.cur_i]
        print cur_groupid
        self.parent.group_to_Iref[cur_groupid] = self.cur_j
    def onButton_jump_page(self, evt):
        dlg = wx.TextEntryDialog(self, "Which Page Number?", "Enter Page number")
        status = dlg.ShowModal()
        if status == wx.ID_CANCEL:
            return
        try:
            idx = int(dlg.GetValue()) - 1
        except:
            print "Invalid index:", idx
            return
        if idx < 0 or idx >= len(self.partitions[self.cur_i][self.cur_j]):
            print "Invalid page index:", idx
            return
        self.display_image(self.cur_i, self.cur_j, idx)

    def infercontests(self):
        def are_there_boxes():
            for i, sides in self.boxes.iteritems():
                if sides:
                    return True
            return False
        if not self.boxsize or not are_there_boxes():
            dlg = wx.MessageDialog(self, style=wx.OK, caption="Can't detect \
contests right now",
                                   message="Please annotate voting targets \
before running the automatic contest detection routine.")
            dlg.ShowModal()
            return
                                   
        if config.TIMER:
            config.TIMER.start_task("SelectTargets_InferContestRegions_CPU")
        imgpaths_exs = [] # list of [imgpath_i, ...]
        # Arbitrarily choose the first one Ballot from each partition
        for partition_idx, imgpaths_sides in enumerate(self.partitions):
            for imgpaths in imgpaths_sides:
                for side, imgpath in enumerate(imgpaths):
                    # Only add imgpaths that have boxes
                    if self.boxes[partition_idx][side]:
                        imgpaths_exs.append(imgpath)
                break
        # Since the ordering of these dataStructs encode semantic meaning,
        # and since I don't want to pass in an empty contest to InferContests
        # (it crashes), I have to manually remove all empty-pages from IMGPATHS_EXS
        # and TARGETS
        # Let i=target #, j=ballot style, k=contest idx:
        targets = [] # list of [[[box_ijk, ...], [box_ijk+1, ...], ...], ...]
        for partition_idx, boxes_sides in self.boxes.iteritems():
            for side, boxes in enumerate(boxes_sides):
                style_boxes = [] # [[contest_i, ...], ...]
                for box in boxes:
                    # InferContests throws out the pre-determined contest
                    # grouping, so just stick each target in its own
                    # 'contest'
                    if type(box) == TargetBox:
                        style_boxes.append([(box.x1, box.y1, box.x2, box.y2)])
                if style_boxes:
                    targets.append(style_boxes)

        # CONTEST_RESULTS: [[box_i, ...], ...], each subtuple_i is for imgpath_i.
        def infercontest_finish(contest_results):
            # 1.) Update my self.BOXES
            for i, contests in enumerate(contest_results):
                partition_idx, j, page = self.inv_map[imgpaths_exs[i]]
            # Remove previous contest boxes
                justtargets = [b for b in self.boxes[partition_idx][page] if not isinstance(b, ContestBox)]
                contest_boxes = []
                for (x1,y1,x2,y2) in contests:
                    contest_boxes.append(ContestBox(x1,y1,x2,y2))
                recolour_contests(contest_boxes)
                self.boxes[partition_idx][page] = justtargets+contest_boxes
        # 2.) Update self.IMAGEPANEL.BOXES (i.e. the UI)
            self.imagepanel.set_boxes(self.boxes[self.cur_i][self.cur_page])
        # 3.) Finally, update the self.proj.infer_bounding_boxes flag, 
        #     so that LabelContests does the right thing.
            self.GetParent().proj.infer_bounding_boxes = True
            self.Refresh()
            if config.TIMER:
                config.TIMER.stop_task("SelectTargets_InferContestRegions_CPU")

        ocrtempdir = self.ocrtempdir

        class RunThread(threading.Thread):
            def __init__(self, *args, **kwargs):
                threading.Thread.__init__(self, *args, **kwargs)
                
            def run(self):
                self.tt = group_contests.find_contests(ocrtempdir, imgpaths_exs, targets)
                wx.CallAfter(Publisher().sendMessage, "signals.MyGauge.done")

        tt = RunThread()
        tt.start()

        gauge = util.MyGauge(self, 1, ondone=lambda: infercontest_finish(tt.tt))
        gauge.Show()
        wx.CallAfter(Publisher().sendMessage, "signals.MyGauge.nextjob", len(imgpaths_exs))

    def set_target_roi(self, roi):
        """ Updates/sets the target region-of-interest (ROI), which is the
        region where the user is expected to 'draw' on. This information is
        useful for the SetThreshold panel, so that it can better-sort the
        voting targets.
        Input:
            tuple ROI: (int x1, y1, x2, y2)
        """
        self.target_roi = tuple([int(round(coord)) for coord in roi])
        return self.target_roi
        
class Toolbar(wx.Panel):
    def __init__(self, parent, *args, **kwargs):
        wx.Panel.__init__(self, parent, *args, **kwargs)
        self.parent = parent
        
        self._setup_ui()
        self._setup_evts()
        self.Layout()

    def _setup_ui(self):
        self.btn_addtarget = wx.Button(self, label="Add Target")
        self.btn_forceaddtarget = wx.Button(self, label="Force Add Target")
        self.btn_addcontest = wx.Button(self, label="Add Contest")
        self.btn_modify = wx.Button(self, label="Modify")
        self.btn_zoomin = wx.Button(self, label="Zoom In")
        self.btn_zoomout = wx.Button(self, label="Zoom Out")
        self.btn_infercontests = wx.Button(self, label="Infer Contest Regions...")
        self.btn_opts = wx.Button(self, label="Advanced: Options")
        self.btn_resize_targets = wx.Button(self, label="Resize Voting Targets")
        self.btn_detect_errors = wx.Button(self, label="Detect Errors")
        self.btn_set_target_roi = wx.Button(self, label="Set Mark Region")
        self.sizer = wx.BoxSizer(wx.VERTICAL)
        btn_sizer = wx.BoxSizer(wx.HORIZONTAL)
        btn_sizer.AddMany([(self.btn_addtarget,), (self.btn_forceaddtarget,), 
                           (self.btn_addcontest), (self.btn_modify,),
                           (self.btn_zoomin,), (self.btn_zoomout,),
                           (self.btn_infercontests,), (self.btn_opts,),
                           (self.btn_resize_targets,), (self.btn_detect_errors,),
                           (self.btn_set_target_roi)])
        self.sizer.Add(btn_sizer)
        self.SetSizer(self.sizer)

    def _setup_evts(self):
        self.btn_addtarget.Bind(wx.EVT_BUTTON, self.onButton_addtarget)
        self.btn_forceaddtarget.Bind(wx.EVT_BUTTON, self.onButton_forceaddtarget)
        self.btn_addcontest.Bind(wx.EVT_BUTTON, self.onButton_addcontest)
        self.btn_modify.Bind(wx.EVT_BUTTON, lambda evt: self.setmode(BoxDrawPanel.M_IDLE))
        self.btn_zoomin.Bind(wx.EVT_BUTTON, lambda evt: self.parent.zoomin())
        self.btn_zoomout.Bind(wx.EVT_BUTTON, lambda evt: self.parent.zoomout())
        self.btn_infercontests.Bind(wx.EVT_BUTTON, lambda evt: self.parent.infercontests())
        self.btn_opts.Bind(wx.EVT_BUTTON, self.onButton_opts)
        self.btn_resize_targets.Bind(wx.EVT_BUTTON, self.onButton_resizetargets)
        self.btn_detect_errors.Bind(wx.EVT_BUTTON, self.onButton_detecterrors)
        self.btn_set_target_roi.Bind(wx.EVT_BUTTON, self.onButton_settargetroi)
    def onButton_addtarget(self, evt):
        self.setmode(BoxDrawPanel.M_CREATE)
        self.parent.imagepanel.boxtype = TargetBox
    def onButton_forceaddtarget(self, evt):
        self.setmode(TargetFindPanel.M_FORCEADD_TARGET)
        self.parent.imagepanel.boxtype = TargetBox
    def onButton_addcontest(self, evt):
        self.setmode(BoxDrawPanel.M_CREATE)
        self.parent.imagepanel.boxtype = ContestBox
    def setmode(self, mode_m):
        self.parent.imagepanel.set_mode_m(mode_m)
    def onButton_opts(self, evt):
        dlg = OptionsDialog(self)
        status = dlg.ShowModal()
        if status == wx.ID_CANCEL:
            return
        self.parent.tm_param = dlg.tm_param
        self.parent.win_ballot = dlg.win_ballot
        self.parent.win_target = dlg.win_target
        self.parent.tm_mode = dlg.tm_mode
    def onButton_resizetargets(self, evt):
        if not self.parent.boxsize:
            wx.MessageDialog(self, style=wx.OK, caption="Must create voting targets first",
                             message="Please first create voting targets on the ballot. \
Then, you may resize the voting targets here.").ShowModal()
            return
        dlg = ResizeTargetsDialog(self, self.parent.boxsize)
        status = dlg.ShowModal()
        if status == wx.ID_CANCEL:
            return
        x1_del, y1_del, x2_del, y2_del = dlg.x1_del, dlg.y1_del, dlg.x2_del, dlg.y2_del
        self.parent.resize_targets(x1_del, y1_del, x2_del, y2_del)
    def onButton_detecterrors(self, evt):
        events = {}
        lookup = {}
        kinds = {}
        votes_for_errors = {}
        stats_by_ballot = {}
        def set_events(ee):
            for e in ee: events[e[0]] = {}
            for e in ee: lookup[e[0]] = {}
            for e in ee: kinds[e[0]] = e[1]
        def observe(e, obs, uid): 
            if obs not in events[e]: 
                events[e][obs] = 0
                lookup[e][obs] = []
            events[e][obs] += 1
            lookup[e][obs].append(uid)
            votes_for_errors[uid] = 0
            if uid not in stats_by_ballot:
                stats_by_ballot[uid] = {}
            stats_by_ballot[uid][e] = obs

        #self.parent.boxes = dict((k,[[z for z in y if z.y1 > 400 or z.y2 > 400] for y in v]) for k,v in self.parent.boxes.items())
        #self.parent.boxes = dict((k,[[z for z in y] for y in v]) for k,v in self.parent.boxes.items())
        
        set_events([("exists", "entropy"),
                    ("target count", "entropy"),
                    ("columns", "entropy"),
                    ("targets by column", "entropy"),
                    ("contest count", "entropy"),
                    ("contests by column", "entropy"),
                    ("contest width", "entropy"), 
                    ("colspread", "smaller")])

        def intersect(line1, line2):
            top = max(line1.y1, line2.y1)
            bottom = min(line1.y2, line2.y2)
            left = max(line1.x1, line2.x1)
            right = min(line1.x2, line2.x2)
            return bottom > top and right > left
        
        for pid,partition in self.parent.boxes.items():
            for i,page in enumerate(partition):
                targets = [x for x in page if type(x) == TargetBox]
                observe("exists", True, (pid,i))
                observe("target count", len(targets), (pid,i))
                if len(targets) == 0: continue
                leftcoord = sorted([x.x1 for x in targets])
                width = abs(targets[0].x1-targets[0].x2)
                def group(leftcoord):
                    cols = [[]]
                    for ii,(x1,x2) in enumerate(zip(leftcoord,leftcoord[1:]+[-1<<30])):
                        cols[-1].append(x1)
                        if abs(x1-x2) > width/2:
                            cols.append([])
                    return cols[:-1]
                cols = group(leftcoord)
                observe("columns", len(cols), (pid,i))
                for val in tuple(map(len,cols)):
                    observe("targets by column", val, (pid,i))
                
                contests = [x for x in page if type(x) == ContestBox]
                if len(contests) == 0: continue

                #observe("exists", tuple([sum([intersect(x,y) for y in contests]) == 1 for x in targets]), (pid,i))
                if not all([sum([intersect(x,y) for y in contests]) == 1 for x in targets]):
                    print "OH NO THIS IS BAD", pid+1, i, [x[1] for x in zip([sum([intersect(x,y) for y in contests]) == 1 for x in targets],targets) if x[0] == False]

                observe("contest width", (max((x.x2-x.x1)/50 for x in contests),min((x.x2-x.x1)/50 for x in contests)), (pid,i))
                    

                observe("contest count", len(contests), (pid,i))
                observe("contests by column", tuple(map(len,group(sorted([x.x1 for x in contests])))), (pid,i))
                #spread = 10*sum([1-scipy.stats.linregress(range(len(col)),col)[2]**2 for col in cols[:-1]])
                #print spread
                #print scipy.stats.linregress(range(len(cols[0])),cols[0])
                #observe("colspread", spread, (pid,i))
        for evtname,obs in events.items():
            evttype = kinds[evtname]
            count = sum(obs.values())
            if evttype == "entropy":
                for what,c in obs.items():
                    for ballot in lookup[evtname][what]:
                        votes_for_errors[ballot] += math.log(float(c)/count)
            elif evttype == "smaller":
                expanded = [k for k,v in obs.items() for _ in range(v)]
                average = np.mean(expanded)
                std = np.std(expanded)
                print average, std
                for what,c in obs.items():
                    for ballot in lookup[evtname][what]:
                        if what > average:
                            votes_for_errors[ballot] += -(float(what)-average)/std*2

        self.parent.next_errors = [x[0] for x in sorted(votes_for_errors.items(), key=lambda x: -x[1])]
        for (ballot,side),votes in sorted(votes_for_errors.items(), key=lambda x: -x[1]):
            print ballot+1, side, votes, stats_by_ballot[ballot,side]
        print events

    def onButton_settargetroi(self, evt):
        if not self.GetParent().boxsize:
            dlg = wx.MessageDialog(self, style=wx.OK,
                                   message="Please select at least one voting \
target first.")
            dlg.ShowModal()
            return
        imgpath = self.GetParent().partitions[0][0][0]
        # boxes: {int i: [[Box_iFront, ...], ...]}
        box = self.GetParent().boxes[0][0][0]
        # targetroi: [int x1, int y1, int x2, int y2]
        targetroi = self.GetParent().target_roi

        I = scipy.misc.imread(imgpath, flatten=True)
        Itarget = I[box.y1:box.y2, box.x1:box.x2]
        
        dlg = DrawROIDialog(self, Itarget, roi=targetroi)
        status = dlg.ShowModal()
        if status == wx.CANCEL:
            return
        # tuple ROI: (int x1, y1, x2, y2)
        roi = dlg.roi

        print "(SelectTargets) Set target_roi from {0} to: {1}".format(self.GetParent().target_roi, roi)
        self.GetParent().set_target_roi(roi)
        
class ResizeTargetsDialog(wx.Dialog):
    def __init__(self, parent, boxsize, *args, **kwargs):
        wx.Dialog.__init__(self, parent, size=(475, 350), title="Resizing Voting Targets",
                           style=wx.CAPTION | wx.RESIZE_BORDER | wx.SYSTEM_MENU, *args, **kwargs)
        
        self.boxsize = boxsize
        self.x1_del, self.y1_del = None, None
        self.x2_del, self.y2_del = None, None

        msg_inst = (textwrap.fill("Please indicate (in pixels) \
how much to shift the x1, y1 (Upper-left corner) and x2, y2 (Lower-right corner) \
by.", 75) + "\n\n" + textwrap.fill("Positive X values shift to the Right, negative X values shift to the Left.", 75)
                    + "\n\n" + textwrap.fill("Positive Y values shift Downwards, negative Y values shift Upward.", 75))

        txt_inst = wx.StaticText(self, label=msg_inst)

        txt_boxsize_old = wx.StaticText(self, label="Current Target Size (width,height): ({0}, {1})".format(boxsize[0], boxsize[1]))
        
        szh_upperleft = wx.BoxSizer(wx.HORIZONTAL)
        txt_upperleft = wx.StaticText(self, label="UpperLeft Corner: ")
        szv_x1y1 = wx.BoxSizer(wx.VERTICAL)

        szh_x1 = wx.BoxSizer(wx.HORIZONTAL)
        txt_x1 = wx.StaticText(self, label="Shift X1 by: ")
        self.txtctrl_x1del = wx.TextCtrl(self, value='0')
        szh_x1.AddMany([(txt_x1,), (self.txtctrl_x1del,)])

        szh_y1 = wx.BoxSizer(wx.HORIZONTAL)
        txt_y1 = wx.StaticText(self, label="Shift Y1 by: ")
        self.txtctrl_y1del = wx.TextCtrl(self, value='0')
        szh_y1.AddMany([(txt_y1,), (self.txtctrl_y1del,)])

        szv_x1y1.AddMany([(szh_x1,), (szh_y1,)])

        szh_upperleft.AddMany([(txt_upperleft,), (szv_x1y1,)])

        szh_lowerright = wx.BoxSizer(wx.HORIZONTAL)
        txt_lowerright = wx.StaticText(self, label="LowerRight Corner: ")
        szv_x2y2 = wx.BoxSizer(wx.VERTICAL)

        szh_x2 = wx.BoxSizer(wx.HORIZONTAL)
        txt_x2 = wx.StaticText(self, label="Shift X2 by: ")
        self.txtctrl_x2del = wx.TextCtrl(self, value='0')
        szh_x2.AddMany([(txt_x2,), (self.txtctrl_x2del,)])

        szh_y2 = wx.BoxSizer(wx.HORIZONTAL)
        txt_y2 = wx.StaticText(self, label="Shift Y2 by: ")
        self.txtctrl_y2del = wx.TextCtrl(self, value='0')
        szh_y2.AddMany([(txt_y2,), (self.txtctrl_y2del,)])

        szv_x2y2.AddMany([(szh_x2,), (szh_y2,)])
        
        szh_lowerright.AddMany([(txt_lowerright,), (szv_x2y2)])

        btn_sizer = wx.BoxSizer(wx.HORIZONTAL)
        btn_ok = wx.Button(self, label="Resize All Targets")
        btn_ok.Bind(wx.EVT_BUTTON, self.onButton_ok)
        btn_cancel = wx.Button(self, label="Cancel")
        btn_cancel.Bind(wx.EVT_BUTTON, lambda e: self.EndModal(wx.ID_CANCEL))
        btn_sizer.AddMany([(btn_ok,), ((30, 0),), (btn_cancel,)])

        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.sizer.Add(txt_inst)
        self.sizer.Add((0, 15))
        self.sizer.Add(txt_boxsize_old, flag=wx.ALIGN_CENTER)
        self.sizer.Add((0, 15))
        self.sizer.AddMany([(szh_upperleft,), (szh_lowerright,)])
        self.sizer.Add((0, 15))
        self.sizer.Add(btn_sizer, flag=wx.ALIGN_CENTER)
        self.SetSizer(self.sizer)
        self.Layout()

    def onButton_ok(self, evt):
        def alert_bad_number(self):
            wx.MessageDialog(self, style=wx.OK,
                             message="Must enter valid integer values for each field.").ShowModal()
        try:
            self.x1_del = int(self.txtctrl_x1del.GetValue())
            self.y1_del = int(self.txtctrl_y1del.GetValue())
            self.x2_del = int(self.txtctrl_x2del.GetValue())
            self.y2_del = int(self.txtctrl_y2del.GetValue())
        except:
            alert_bad_number()
            return
        self.EndModal(wx.ID_OK)

class OptionsDialog(wx.Dialog):
    ID_APPLY = 42

    def __init__(self, parent, *args, **kwargs):
        wx.Dialog.__init__(self, parent, title="Options.", *args, **kwargs)
        self.parent = parent

        self.tm_param = None
        self.win_ballot = None
        self.win_target = None

        txt0 = wx.StaticText(self, label="Options for Template Matching.")

        tm_sizer = wx.BoxSizer(wx.HORIZONTAL)
        txt1 = wx.StaticText(self, label="Template Matching sensitivity: ")
        _val = str(self.parent.parent.tm_param)
        self.tm_param = wx.TextCtrl(self, value=_val)
        tm_sizer.AddMany([(txt1,), (self.tm_param,)])
        
        txt00 = wx.StaticText(self, label="Ballot Smoothing parameters (must be odd-integers).")
        txt01 = wx.StaticText(self, label="X-window size: ")
        txt02 = wx.StaticText(self, label="Y-window size: ")
        _val = str(self.parent.parent.win_ballot[0])
        self.xwin_ballot = wx.TextCtrl(self, value=_val)
        _val = str(self.parent.parent.win_ballot[1])        
        self.ywin_ballot = wx.TextCtrl(self, value=_val)
        sizer00 = wx.BoxSizer(wx.HORIZONTAL)
        sizer00.AddMany([(txt01,), (self.xwin_ballot,)])
        sizer01 = wx.BoxSizer(wx.HORIZONTAL)
        sizer01.AddMany([(txt02,), (self.ywin_ballot,)])
        sizer0 = wx.BoxSizer(wx.VERTICAL)
        sizer0.AddMany([(txt00,), (sizer00,), (sizer01,)])

        txt10 = wx.StaticText(self, label="Target Smoothing parameters (must be odd-integers)")
        txt11 = wx.StaticText(self, label="X-window size: ")
        txt12 = wx.StaticText(self, label="Y-window size: ")
        _val = str(self.parent.parent.win_target[0])
        self.xwin_target = wx.TextCtrl(self, value=_val)
        _val = str(self.parent.parent.win_target[1])
        self.ywin_target = wx.TextCtrl(self, value=_val)
        sizer10 = wx.BoxSizer(wx.HORIZONTAL)
        sizer10.AddMany([(txt11,), (self.xwin_target,)])
        sizer11 = wx.BoxSizer(wx.HORIZONTAL)
        sizer11.AddMany([(txt12,), (self.ywin_target,)])
        sizer1 = wx.BoxSizer(wx.VERTICAL)
        sizer1.AddMany([(txt10,), (sizer10,), (sizer11,)])

        txt_tm_mode = wx.StaticText(self, label="Template Matching Mode")
        self.radio_tm_mode_all = wx.RadioButton(self, label="Template match on all images", 
                                                style=wx.RB_GROUP)
        self.radio_tm_mode_post = wx.RadioButton(self, label="Template match only on images \
after (and including) the currently-displayed group.")
        if self.GetParent().GetParent().tm_mode == SelectTargetsPanel.TM_MODE_ALL:
            self.radio_tm_mode_all.SetValue(True)
        elif self.GetParent().GetParent().tm_mode == SelectTargetsPanel.TM_MODE_POST:
            self.radio_tm_mode_post.SetValue(True)
        sizer_tm_mode = wx.BoxSizer(wx.VERTICAL)
        sizer_tm_mode.AddMany([(txt_tm_mode,), (self.radio_tm_mode_all,),
                               (self.radio_tm_mode_post,)])

        btn_apply = wx.Button(self, label="Apply")
        btn_apply.Bind(wx.EVT_BUTTON, self.onButton_apply)
        btn_cancel = wx.Button(self, label="Cancel")
        btn_cancel.Bind(wx.EVT_BUTTON, self.onButton_cancel)
        btn_sizer = wx.BoxSizer(wx.HORIZONTAL)
        btn_sizer.AddMany([(btn_apply,), (btn_cancel,)])
        
        sizer = wx.BoxSizer(wx.VERTICAL)
        sizer.Add(txt0, flag=wx.ALIGN_CENTER)
        sizer.AddMany([(tm_sizer,), (sizer0,), (sizer1,), (sizer_tm_mode,), (btn_sizer, 0, wx.ALIGN_CENTER)])
        self.SetSizer(sizer)
        self.Fit()

    def onButton_apply(self, evt):
        self.tm_param = float(self.tm_param.GetValue())
        self.win_ballot = (int(self.xwin_ballot.GetValue()), int(self.ywin_ballot.GetValue()))
        self.win_target = (int(self.xwin_target.GetValue()), int(self.ywin_target.GetValue()))
        if self.radio_tm_mode_all.GetValue():
            self.tm_mode = SelectTargetsPanel.TM_MODE_ALL
        else:
            self.tm_mode = SelectTargetsPanel.TM_MODE_POST
        self.EndModal(OptionsDialog.ID_APPLY)
    def onButton_cancel(self, evt):
        self.EndModal(wx.ID_CANCEL)

class ImagePanel(ScrolledPanel):
    """ Basic widget class that display one image out of N image paths.
    Also comes with a 'Next' and 'Previous' button. Extend me to add
    more functionality (i.e. mouse-related events).
    """
    def __init__(self, parent, *args, **kwargs):
        ScrolledPanel.__init__(self, parent, *args, **kwargs)
        self.parent = parent

        # self.img := a WxImage
        self.img = None
        # self.imgbitmap := A WxBitmap
        self.imgbitmap = None
        # self.npimg := A Numpy-version of an untarnished-version of self.imgbitmap
        self.npimg = None

        # self.scale: Scaling factor used to display self.IMGBITMAP
        self.scale = 1.0

        # If True, a signal to completely-redraw the original image
        self._imgredraw = False

        self._setup_ui()
        self._setup_evts()

    def _setup_ui(self):
        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.SetSizer(self.sizer)

    def _setup_evts(self):
        self.Bind(wx.EVT_PAINT, self.onPaint)
        self.Bind(wx.EVT_LEFT_DOWN, self.onLeftDown)
        self.Bind(wx.EVT_LEFT_UP, self.onLeftUp)
        self.Bind(wx.EVT_MOTION, self.onMotion)
        self.Bind(wx.EVT_CHILD_FOCUS, self.onChildFocus)
        
    def set_image(self, img, size=None):
        """ Updates internal data-structures to allow viewing a new input
        IMG. If SIZE is given (width, height), then we will scale image
        to match SIZE, maintaining aspect ratio.
        """
        self.img = img
        
        c = size[0] / float(self.img.GetWidth()) if size else self.scale
        self.set_scale(c)
        
    def set_scale(self, scale):
        """ Changes scale, i.e. to acommodate zoom in/out. Mutates the
        self.IMGBITMAP.
        Input:
            float scale: Smaller values -> zoomed out images.
        """
        self.scale = scale
        w, h = self.img.GetWidth(), self.img.GetHeight()
        new_w, new_h = int(round(w*scale)), int(round(h*scale))
        self.imgbitmap = img_to_wxbitmap(self.img, (new_w, new_h))
        self.npimg = wxBitmap2np_v2(self.imgbitmap, is_rgb=True)

        self.sizer.Detach(0)
        self.sizer.Add(self.imgbitmap.GetSize())
        self.SetupScrolling()

        self.Refresh()

    def zoomin(self, amt=0.1):
        self.set_scale(self.scale + amt)
    def zoomout(self, amt=0.1):
        self.set_scale(self.scale - amt)

    def client_to_imgcoord(self, x, y):
        """ Transforms client (widget) coordinates to the Image
        coordinate system -- i.e. accounts for image scaling.
        Input:
            int (x,y): Client (UI) Coordinates.
        Output:
            int (X,Y), image coordinates.
        """
        return (int(round(x/self.scale)), int(round(y/self.scale)))
    def c2img(self, x, y):
        """ Convenience method to self.CLIENT_TO_IMGCOORD. """
        return self.client_to_imgcoord(x,y)
    def img_to_clientcoord(self, x, y):
        """ Transforms Image coords to client (widget) coords -- i.e.
        accounts for image scaling.
        Input:
            int (X,Y): Image coordinates.
        Output:
            int (x,y): Client (UI) coordinates.
        """
        return (int(round(x*self.scale)), int(round(y*self.scale)))
    def img2c(self, x, y):
        return self.img_to_clientcoord(x,y)

    def force_new_img_redraw(self):
        """ Forces this widget to completely-redraw self.IMG, even if
        self.imgbitmap contains modifications.
        """
        self._imgredraw = True

    def draw_image(self, dc):
        if not self.imgbitmap:
            return
        if self._imgredraw:
            # Draw the 'virgin' self.img
            self._imgredraw = False
            w, h = self.img.GetWidth(), self.img.GetHeight()
            new_w, new_h = int(round(w*self.scale)), int(round(h*self.scale))
            self.imgbitmap = img_to_wxbitmap(self.img, (new_w, new_h))

        dc.DrawBitmap(self.imgbitmap, 0, 0)
        return dc

    def onPaint(self, evt):
        if self.IsDoubleBuffered():
            dc = wx.PaintDC(self)
        else:
            dc = wx.BufferedPaintDC(self)
        self.PrepareDC(dc)
        self.draw_image(dc)

        return dc

    def onLeftDown(self, evt):
        x, y = self.CalcUnscrolledPosition(evt.GetPositionTuple())
        evt.Skip()

    def onMotion(self, evt):
        evt.Skip()

    def onChildFocus(self, evt):
        # If I don't override this child focus event, then wx will
        # reset the scrollbars at extremely annoying times. Weird.
        # For inspiration, see:
        #    http://wxpython-users.1045709.n5.nabble.com/ScrolledPanel-mouse-click-resets-scrollbars-td2335368.html
        pass

class BoxDrawPanel(ImagePanel):
    """ A widget that allows a user to draw boxes on a displayed image,
    and each image remembers its list of boxes.
    """

    """ Mouse Mouse:
        M_CREATE: Create a box on LeftDown.
        M_IDLE: Allow user to resize/move/select(multiple) boxes.
    """
    M_CREATE = 0
    M_IDLE = 1

    def __init__(self, parent, *args, **kwargs):
        ImagePanel.__init__(self, parent, *args, **kwargs)
        self.parent = parent

        # self.boxes := [Box_i, ...]
        self.boxes = []

        # self.sel_boxes := [Box_i, ...]
        self.sel_boxes = []

        # Vars to keep track of box-being-created
        self.isCreate = False
        self.box_create = None

        # Vars for resizing behavior
        self.isResize = False
        self.box_resize = None
        self.resize_orient = None # 'N', 'NE', etc...

        # self.isDragging : Is the user moving-mouse while mouse-left-down
        # is held down?
        self.isDragging = False

        self.mode_m = BoxDrawPanel.M_CREATE

        # BOXTYPE: Class of the Box to create
        self.boxtype = Box
        
        # _x,_y keep track of last mouse position
        self._x, self._y = 0, 0

    def _setup_evts(self):
        ImagePanel._setup_evts(self)
        self.Bind(wx.EVT_KEY_DOWN, self.onKeyDown)

    def set_mode_m(self, mode):
        """ Sets my MouseMode. """
        self.mode_m = mode
        self.update_cursor()

    def update_cursor(self, force_cursor=None):
        """ Updates the mouse cursor depending on the current state.
        Returns the wx.Cursor that it decides to set.
        To force the mouse cursor, pass in a wx.Cursor as FORCE_CURSOR.
        """
        if force_cursor != None:
            self.SetCursor(force_cursor)
            return force_cursor
        if self.mode_m == BoxDrawPanel.M_CREATE:
            cursor = wx.StockCursor(wx.CURSOR_CROSS)
        elif self.mode_m == BoxDrawPanel.M_IDLE:
            if self.isResize:
                cursor = wx.StockCursor(wx.CURSOR_SIZING)
            elif self.get_box_to_resize(self._x, self._y)[0]:
                cursor = wx.StockCursor(wx.CURSOR_SIZING)
            elif self.get_boxes_within(self._x, self._y, mode='any'):
                cursor = wx.StockCursor(wx.CURSOR_HAND)
            else:
                cursor = wx.StockCursor(wx.CURSOR_ARROW)
        else:
            cursor = wx.StockCursor(wx.CURSOR_ARROW)
        if self.GetCursor() != cursor:
            self.SetCursor(cursor)
        return cursor

    def set_boxes(self, boxes):
        self.boxes = boxes
        self.dirty_all_boxes()

    def startBox(self, x, y, boxtype=None):
        """ Starts creating a box at (x,y). """
        if boxtype == None:
            boxtype = self.boxtype
        print "...Creating Box: {0}, {1}".format((x,y), boxtype)
        self.isCreate = True
        self.box_create = boxtype(x, y, x+1, y+1)
        # Map Box coords to Image coords, not UI coords.
        self.box_create.scale(1 / self.scale)

    def finishBox(self, x, y):
        """ Finishes box creation at (x,y). """
        print "...Finished Creating Box:", (x,y)
        self.isCreate = False
        # 0.) Canonicalize box coords s.t. order is: UpperLeft, LowerRight.
        self.box_create.canonicalize()
        toreturn = self.box_create
        self.box_create = None
        self.dirty_all_boxes()
        return toreturn

    def set_scale(self, scale, *args, **kwargs):
        self.dirty_all_boxes()
        return ImagePanel.set_scale(self, scale, *args, **kwargs)

    def dirty_all_boxes(self):
        """ Signal to unconditionally-redraw all boxes. """
        for box in self.boxes:
            box._dirty = True
    
    def select_boxes(self, *boxes):
        for box in boxes:
            box.is_sel = True
        self.sel_boxes.extend(boxes)
        self.dirty_all_boxes()

    def clear_selected(self):
        """ Un-selects all currently-selected boxes, if any. """
        for box in self.sel_boxes:
            box.is_sel = False
        self.sel_boxes = []

    def delete_boxes(self, *boxes):
        """ Deletes the boxes in BOXES. """
        for box in boxes:
            self.boxes.remove(box)
            if box in self.sel_boxes:
                self.sel_boxes.remove(box)
        self.dirty_all_boxes()
        if not self.boxes:
            # Force a redraw of the image - otherwise, the last-removed
            # boxes don't go away.
            self.force_new_img_redraw()
            self.Refresh()

    def get_boxes_within(self, x, y, C=8.0, mode='any'):
        """ Returns a list of Boxes that are at most C units within
        the position (x,y), sorted by distance (increasing).
        Input:
            int (x,y):
        Output:
            list MATCHES, of the form:
                [(obj Box_i, float dist_i), ...]
        """

        results = []
        for box in self.boxes:
            if mode == 'N':
                x1, y1 = self.img2c((box.x1 + (box.width/2)), box.y1)
            elif mode == 'NE':
                x1, y1 = self.img2c(box.x1 + box.width, box.y1)
            elif mode == 'E':
                x1, y1 = self.img2c(box.x1 + box.width, box.y1 + (box.height/2))
            elif mode == 'SE':
                x1, y1 = self.img2c(box.x1 + box.width, box.y1 + box.height)
            elif mode == 'S':
                x1, y1 = self.img2c(box.x1 + (box.width/2), box.y1 + box.height)
            elif mode == 'SW':
                x1, y1 = self.img2c(box.x1, box.y1 + box.height)
            elif mode == 'W':
                x1, y1 = self.img2c(box.x1, box.y1 + (box.heigth/2))
            elif mode == 'NW':
                x1, y1 = self.img2c(box.x1, box.y1)
            else:
                # Default to 'any'
                x1, y1 = self.img2c(box.x1, box.y1)
                x2, y2 = self.img2c(box.x2, box.y2)
                if (x > x1 and x < x2 and
                    y > y1 and y < y2):
                    results.append((box, None))
                continue
            dist = distL2(x1, y1, x, y)
            if dist <= C:
                results.append((box, dist))
        if mode == 'any':
            return results
        results = sorted(results, key=lambda t: t[1])
        return results

    def get_box_to_resize(self, x, y, C=5.0):
        """ Returns a Box instance if the current mouse location is
        close enough to a resize location, or None o.w.
        Input:
            int X, Y: Mouse location.
            int C: How close the mouse has to be to a box corner.
        Output:
            (Box, str orientation) or (None, None).
        """
        results = [] # [[orient, box, dist], ...]
        for box in self.boxes:
            locs = {'N': self.img2c(box.x1 + (box.width/2), box.y1),
                    'NE': self.img2c(box.x1 + box.width, box.y1),
                    'E': self.img2c(box.x1 + box.width, box.y1 + (box.height/2)),
                    'SE': self.img2c(box.x1 + box.width, box.y1 + box.height),
                    'S': self.img2c(box.x1 + (box.width/2),box.y1 + box.height),
                    'SW': self.img2c(box.x1, box.y1 + box.height),
                    'W': self.img2c(box.x1, box.y1 + (box.height/2)),
                    'NW': self.img2c(box.x1, box.y1)}
            for (orient, (x1,y1)) in locs.iteritems():
                dist = distL2(x1,y1,x,y)
                if dist <= C:
                    results.append((orient, box, dist))
        if not results:
            return None, None
        results = sorted(results, key=lambda t: t[2])
        return results[0][1], results[0][0]

    def onLeftDown(self, evt):
        self.SetFocus()
        x, y = self.CalcUnscrolledPosition(evt.GetPositionTuple())
        x_img, y_img = self.c2img(x,y)
        w_img, h_img = self.img.GetSize()
        if x_img >= (w_img-1) or y_img >= (h_img-1):
            return

        box_resize, orient = self.get_box_to_resize(x, y)
        if self.mode_m == BoxDrawPanel.M_IDLE and box_resize:
            self.isResize = True
            self.box_resize = box_resize
            self.resize_orient = orient
            self.Refresh()
            self.update_cursor()
            return

        if self.mode_m == BoxDrawPanel.M_CREATE:
            print "...Creating Target box."
            self.clear_selected()
            self.startBox(x, y)
            self.update_cursor()
        elif self.mode_m == BoxDrawPanel.M_IDLE:
            boxes = self.get_boxes_within(x, y, mode='any')
            if boxes:
                b = boxes[0][0]
                if b not in self.sel_boxes:
                    self.clear_selected()
                    self.select_boxes(boxes[0][0])
            else:
                self.clear_selected()
                self.startBox(x, y, SelectionBox)
            self.update_cursor()

    def onLeftUp(self, evt):
        x, y = self.CalcUnscrolledPosition(evt.GetPositionTuple())
        self.isDragging = False
        if self.isResize:
            self.box_resize.canonicalize()
            self.box_resize = None
            self.isResize = False
            self.dirty_all_boxes()
            self.update_cursor()

        if self.mode_m == BoxDrawPanel.M_CREATE and self.isCreate:
            box = self.finishBox(x, y)
            self.boxes.append(box)
            self.update_cursor()
        elif self.mode_m == BoxDrawPanel.M_IDLE and self.isCreate:
            box = self.finishBox(x, y)
            boxes = get_boxes_within(self.boxes, box)
            print "...Selecting {0} boxes.".format(len(boxes))
            self.select_boxes(*boxes)
            self.update_cursor()
        
        self.Refresh()

    def onMotion(self, evt):
        x, y = self.CalcUnscrolledPosition(evt.GetPositionTuple())
        xdel, ydel = x - self._x, y - self._y
        self._x, self._y = x, y
        
        if self.isResize and evt.Dragging():
            xdel_img, ydel_img = self.c2img(xdel, ydel)
            if 'N' in self.resize_orient:
                self.box_resize.y1 += ydel_img
            if 'E' in self.resize_orient:
                self.box_resize.x2 += xdel_img
            if 'S' in self.resize_orient:
                self.box_resize.y2 += ydel_img
            if 'W' in self.resize_orient:
                self.box_resize.x1 += xdel_img
            self.update_cursor()
            self.Refresh()
            return

        if self.isCreate:
            self.box_create.x2, self.box_create.y2 = self.c2img(x, y)
            self.Refresh()
        elif self.sel_boxes and evt.Dragging():
            self.isDragging = True
            xdel_img, ydel_img = self.c2img(xdel, ydel)
            for box in self.sel_boxes:
                box.x1 += xdel_img
                box.y1 += ydel_img
                box.x2 += xdel_img
                box.y2 += ydel_img
            # Surprisingly, forcing a redraw for each mouse mvmt. is
            # a very fast operation! Very convenient.
            self.dirty_all_boxes()
            self.Refresh()
        self.update_cursor()

    def onKeyDown(self, evt):
        keycode = evt.GetKeyCode()
        if (keycode == wx.WXK_DELETE or keycode == wx.WXK_BACK):
            self.delete_boxes(*self.sel_boxes)
            self.Refresh()
        elif ((keycode in (wx.WXK_UP, wx.WXK_DOWN, wx.WXK_LEFT, wx.WXK_RIGHT))
              and self.sel_boxes):
            xdel, ydel = 0, 0
            if keycode == wx.WXK_UP:
                ydel -= 1
            elif keycode == wx.WXK_DOWN:
                ydel += 1
            elif keycode == wx.WXK_LEFT:
                xdel -= 1
            else:
                xdel += 1
            xdel_img, ydel_img = self.c2img(xdel, ydel)
            for box in self.sel_boxes:
                box.x1 += xdel_img
                box.y1 += ydel_img
                box.x2 += xdel_img
                box.y2 += ydel_img
            self.dirty_all_boxes()
            self.Refresh()
            

    def onPaint(self, evt):
        total_t = time.time()
        dc = ImagePanel.onPaint(self, evt)
        if self.isResize:
            dboxes = [b for b in self.boxes if b != self.box_resize]
        else:
            dboxes = self.boxes
        t = time.time()
        self.drawBoxes(dboxes, dc)
        dur = time.time() - t
        if self.isCreate:
            # Draw Box-Being-Created
            can_box = self.box_create.copy().canonicalize()
            self.drawBox(can_box, dc)
        if self.isResize:
            resize_box_can = self.box_resize.copy().canonicalize()
            self.drawBox(resize_box_can, dc)
        total_dur = time.time() - total_t
        #print "Total Time: {0:.5f}s  (drawBoxes: {1:.5f}s, {2:.4f}%)".format(total_dur, dur, 100*float(dur / total_dur))
        return dc
        
    def drawBoxes(self, boxes, dc):
        boxes_todo = [b for b in boxes if b._dirty]
        if not boxes_todo:
            return
        # First draw contests, then targets on-top.
        contest_boxes, target_boxes = [], []
        for box in boxes_todo:
            if isinstance(box, ContestBox):
                contest_boxes.append(box)
            else:
                target_boxes.append(box)

        npimg_cpy = self.npimg.copy()
        def draw_border(npimg, box, thickness=2, color=(0, 0, 0)):
            T = thickness
            clr = np.array(color)
            x1,y1,x2,y2 = box.x1, box.y1, box.x2, box.y2
            x1,y1 = self.img2c(x1,y1)
            x2,y2 = self.img2c(x2,y2)
            x1 = max(x1, 0)
            y1 = max(y1, 0)
            # Top
            npimg[y1:y1+T, x1:x2] *= 0.2
            npimg[y1:y1+T, x1:x2] += clr*0.8
            # Bottom
            npimg[max(0, (y2-T)):y2, x1:x2] *= 0.2
            npimg[max(0, (y2-T)):y2, x1:x2] += clr*0.8
            # Left
            npimg[y1:y2, x1:(x1+T)] *= 0.2
            npimg[y1:y2, x1:(x1+T)] += clr*0.8
            # Right
            npimg[y1:y2, max(0, (x2-T)):x2] *= 0.2
            npimg[y1:y2, max(0, (x2-T)):x2] += clr*0.8
            return npimg

        # Handle legacy-ContestBoxes that don't have the .colour property
        # TODO: This can be eventually removed. This is more for internal
        #       purposes, to not crash-and-burn on projects created before
        #       this feature was pushed to the repo. Harmless to leave in.
        if contest_boxes and not hasattr(contest_boxes[0], 'colour'):
            recolour_contests(contest_boxes)

        for i, contestbox in enumerate(contest_boxes):
            clr, thickness = contestbox.get_draw_opts()
            draw_border(npimg_cpy, contestbox, thickness=thickness, color=(0, 0, 0))
            if contestbox.is_sel:
                transparent_color = np.array(contestbox.shading_selected_clr) if contestbox.shading_selected_clr else None
            else:
                transparent_color = np.array(contestbox.colour) if contestbox.colour else None
            if transparent_color != None:
                t = time.time()
                _x1, _y1 = self.img2c(contestbox.x1, contestbox.y1)
                _x2, _y2 = self.img2c(contestbox.x2, contestbox.y2)
                np_rect = npimg_cpy[max(0, _y1):_y2, max(0, _x1):_x2]
                np_rect[:,:] *= 0.7
                np_rect[:,:] += transparent_color*0.3
                dur_wxbmp2np = time.time() - t
            
            contestbox._dirty = False

        for targetbox in target_boxes:
            clr, thickness = targetbox.get_draw_opts()
            draw_border(npimg_cpy, targetbox, thickness=thickness, color=(0, 0, 0))
            if targetbox.is_sel:
                transparent_color = np.array(targetbox.shading_selected_clr) if targetbox.shading_selected_clr else None
            else:
                transparent_color = np.array(targetbox.shading_clr) if targetbox.shading_clr else None
            if transparent_color != None:
                t = time.time()
                _x1, _y1 = self.img2c(targetbox.x1, targetbox.y1)
                _x2, _y2 = self.img2c(targetbox.x2, targetbox.y2)
                np_rect = npimg_cpy[max(0, _y1):_y2, max(0, _x1):_x2]
                np_rect[:,:] *= 0.7
                np_rect[:,:] += transparent_color*0.3
                dur_wxbmp2np = time.time() - t
            
            targetbox._dirty = False

        h, w = npimg_cpy.shape[:2]
        t = time.time()
        _image = wx.EmptyImage(w, h)
        _image.SetData(npimg_cpy.tostring())
        bitmap = _image.ConvertToBitmap()
        dur_img2bmp = time.time() - t

        self.imgbitmap = bitmap
        self.Refresh()

    def drawBox(self, box, dc):
        """ Draws BOX onto DC.
        Note: This draws directly to the PaintDC - this should only be done
        for user-driven 'dynamic' behavior (such as resizing a box), as
        drawing to the DC is much slower than just blitting everything to
        the self.imgbitmap.
        self.drawBoxes does all heavy-lifting box-related drawing in a single
        step.
        Input:
            list box: (x1, y1, x2, y2)
            wxDC DC:
        """
        total_t = time.time()

        t = time.time()
        dc.SetBrush(wx.TRANSPARENT_BRUSH)
        drawops = box.get_draw_opts()
        dc.SetPen(wx.Pen(*drawops))
        w = int(round(abs(box.x2 - box.x1) * self.scale))
        h = int(round(abs(box.y2 - box.y1) * self.scale))
        client_x, client_y = self.img2c(box.x1, box.y1)
        dc.DrawRectangle(client_x, client_y, w, h)
        dur_drawrect = time.time() - t

        transparent_color = np.array([200, 0, 0]) if isinstance(box, TargetBox) else np.array([0, 0, 200])
        if self.imgbitmap and type(box) in (TargetBox, ContestBox):
            t = time.time()
            _x1, _y1 = self.img2c(box.x1, box.y1)
            _x2, _y2 = self.img2c(box.x2, box.y2)
            _x1, _y1 = max(0, _x1), max(0, _y1)
            _x2, _y2 = min(self.imgbitmap.Width-1, _x2), min(self.imgbitmap.Height-1, _y2)
            if (_x2 - _x1) <= 1 or (_y2 - _y1) <= 1:
                return
            sub_bitmap = self.imgbitmap.GetSubBitmap((_x1, _y1, _x2-_x1, _y2-_y1))
            # I don't think I need to do a .copy() here...
            #np_rect = wxBitmap2np_v2(sub_bitmap, is_rgb=True).copy()
            np_rect = wxBitmap2np_v2(sub_bitmap, is_rgb=True)
            np_rect[:,:] *= 0.7
            np_rect[:,:] += transparent_color*0.3
            dur_wxbmp2np = time.time() - t

            _h, _w, channels = np_rect.shape

            t = time.time()
            _image = wx.EmptyImage(_w, _h)
            _image.SetData(np_rect.tostring())
            bitmap = _image.ConvertToBitmap()
            dur_img2bmp = time.time() - t

            t = time.time()
            memdc = wx.MemoryDC()
            memdc.SelectObject(bitmap)
            dc.Blit(client_x, client_y, _w, _h, memdc, 0, 0)
            memdc.SelectObject(wx.NullBitmap)
            dur_memdcBlit = time.time() - t

        t = time.time()
        if isinstance(box, TargetBox) or isinstance(box, ContestBox):
            # Draw the 'grabber' circles
            CIRCLE_RAD = 2
            dc.SetPen(wx.Pen("Black", 1))
            dc.SetBrush(wx.Brush("White"))
            dc.DrawCircle(client_x, client_y, CIRCLE_RAD)           # Upper-Left
            dc.DrawCircle(client_x+(w/2), client_y, CIRCLE_RAD)     # Top
            dc.DrawCircle(client_x+w, client_y, CIRCLE_RAD)         # Upper-Right
            dc.DrawCircle(client_x, client_y+(h/2), CIRCLE_RAD)     # Left
            dc.DrawCircle(client_x+w, client_y+(h/2), CIRCLE_RAD)   # Right
            dc.DrawCircle(client_x, client_y+h, CIRCLE_RAD)         # Lower-Left
            dc.DrawCircle(client_x+(w/2), client_y+h, CIRCLE_RAD)     # Bottom
            dc.DrawCircle(client_x+w, client_y+h, CIRCLE_RAD)           # Lower-Right
            dc.SetBrush(wx.TRANSPARENT_BRUSH)

        dur_drawgrabbers = time.time() - t

        total_dur = time.time() - total_t

        '''
        print "== drawBox Total {0:.6f}s (wxbmp2np: {1:.6f}s {2:.3f}%) \
(_img2bmp: {3:.6f}s {4:.3f}%) (memdc.blit {5:.3f}s {6:.3f}%) \
(drawrect: {7:.6f}s {8:.3f}%) (drawgrabbers {9:.6f} {10:.3f}%)".format(total_dur,
                                                                      dur_wxbmp2np,
                                                                      100*(dur_wxbmp2np / total_dur),
                                                                      dur_img2bmp,
                                                                      100*(dur_img2bmp / total_dur),
                                                                      dur_memdcBlit,
                                                                      100*(dur_memdcBlit / total_dur),
                                                                      dur_drawrect,
                                                                      100*(dur_drawrect / total_dur),
                                                                      dur_drawgrabbers,
                                                                      100*(dur_drawgrabbers / total_dur))
        '''
                                                                 
class TemplateMatchDrawPanel(BoxDrawPanel):
    """ Like a BoxDrawPanel, but when you create a Target box, it runs
    Template Matching to try to find similar instances.
    """
    def __init__(self, parent, tempmatch_fn, *args, **kwargs):
        BoxDrawPanel.__init__(self, parent, *args, **kwargs)
        self.parent = parent
        self.tempmatch_fn = tempmatch_fn

    def onLeftUp(self, evt):
        x, y = self.CalcUnscrolledPosition(evt.GetPositionTuple())
        MIN_LEN = 13
        if self.mode_m == BoxDrawPanel.M_CREATE and self.isCreate:
            x_img, y_img = self.c2img(x,y)
            if (abs(self.box_create.x1 - x_img) <= MIN_LEN) or (abs(self.box_create.y1 - y_img) <= MIN_LEN):
                print "...User drew a too-small box..."
                dlg = wx.MessageDialog(self, style=wx.YES_NO | wx.NO_DEFAULT,
                                       message="You drew a box that \
was a bit small. \n\n\
Would you still like to use this box? If so, then choose the 'Yes' button. \n\n\
Otherwise, if this box was created by mistake, and you would like to \
create a better box around a voting target, then choose the 'No' button.")
                self.Disable()
                status = dlg.ShowModal()
                self.Enable()
                if status == wx.ID_NO:
                    self.isCreate = False
                    self.box_create = None
                    self.Refresh()
                    return

            box = self.finishBox(x, y)
            if isinstance(box, TargetBox):
                imgpil = util_gui.imageToPil(self.img)
                imgpil = imgpil.convert('L')
                targetimg_prefit = imgpil.crop((box.x1, box.y1, box.x2, box.y2))
                targetimg_crop = util_gui.fit_image(targetimg_prefit, padx=2, pady=2)
                if self.GetParent().boxsize == None:
                    # First time user drew a box
                    print "(SelectTargets) First target selected."
                    targetimg_crop_np = np.array(targetimg_crop)
                    dlg = DrawROIDialog(self, targetimg_crop_np)
                    status = dlg.ShowModal()
                    if status == wx.CANCEL:
                        return
                    # tuple ROI: (int x1, y1, x2, y2)
                    roi = dlg.roi
                    print "(SelectTargets) Set target_roi from {0} to: {1}".format(self.GetParent().target_roi, roi)
                    self.GetParent().set_target_roi(roi)
        
                self.tempmatch_fn(box, imgpil, patch=targetimg_crop)
            elif isinstance(box, ContestBox):
                self.boxes.append(box)
            self.Refresh()
        else:
            BoxDrawPanel.onLeftUp(self, evt)

class TargetFindPanel(TemplateMatchDrawPanel):
    M_FORCEADD_TARGET = 3

    def finishBox(self, *args, **kwargs):
        toret = TemplateMatchDrawPanel.finishBox(self, *args, **kwargs)
        if isinstance(toret, ContestBox):
            recolour_contests([b for b in self.boxes if isinstance(b, ContestBox)]+[toret])
            self.dirty_all_boxes()
        self.Refresh()
        return toret

    def update_cursor(self, *args, **kwargs):
        if self.mode_m == TargetFindPanel.M_FORCEADD_TARGET:
            cursor = wx.StockCursor(wx.CURSOR_CROSS)
            self.SetCursor(cursor)
            return cursor
        return TemplateMatchDrawPanel.update_cursor(self, *args, **kwargs)

    def onLeftDown(self, evt):
        x, y = self.CalcUnscrolledPosition(evt.GetPositionTuple())
        x_img, y_img = self.c2img(x,y)
        w_img, h_img = self.img.GetSize()
        if x_img >= (w_img-1) or y_img >= (h_img-1):
            return
                                                        
        if self.mode_m == self.M_FORCEADD_TARGET:
            print "...Creating Forced Target."
            self.clear_selected()
            self.startBox(x, y)
            self.Refresh()
            self.update_cursor()
        else:
            TemplateMatchDrawPanel.onLeftDown(self, evt)

    def onLeftUp(self, evt):
        x, y = self.CalcUnscrolledPosition(evt.GetPositionTuple())
        # Restrict (x,y) to lie within the image
        w_img, h_img = self.img.GetSize()
        w_c, h_c = self.img2c(w_img-1, h_img-1)
        x = min(w_c, x)
        y = min(h_c, y)
        if self.mode_m == self.M_FORCEADD_TARGET and self.isCreate:
            # If this is the first-created box B, then make sure that 
            # subsequent-created boxes match the dimensions of B
            box = self.finishBox(x, y)
            if self.GetParent().boxsize == None:
                self.GetParent().boxsize = (box.width, box.height)
            else:
                w, h = self.GetParent().boxsize
                box.x2 = box.x1 + w
                box.y2 = box.y1 + h
            self.boxes.append(box)
            self.Refresh()
            self.update_cursor()
        else:
            TemplateMatchDrawPanel.onLeftUp(self, evt)

class DrawROIDialog(wx.Dialog):
    """ A simple dialog that displays an image, and the user either:
        a.) Draws a sub-box within the image
    or:
        b.) Cancels the action.
    """
    def __init__(self, parent, npimg, roi=None, *args, **kwargs):
        wx.Dialog.__init__(self, parent, title="Draw Target Region-of-Interest", size=(600, 400),
                           style=wx.RESIZE_BORDER | wx.CAPTION | wx.MAXIMIZE_BOX | wx.MINIMIZE_BOX, *args, **kwargs)
        if npimg.dtype != 'uint8':
            npimg = npimg.astype('uint8')
        self.npimg = gray2rgb_np(npimg)
        h, w = npimg.shape[:2]
        self.wximg = wx.ImageFromBuffer(w, h, self.npimg)

        # tuple ROI: (int x1, y1, x2, y2)
        self.roi = None

        txt_inst = (textwrap.fill("Displayed is the selected region.", 75) + "\n" +
                    textwrap.fill("Please select the subregion of \
the voting target where voter marks are expected to be made.", 75))
        stxt_inst = wx.StaticText(self, label=txt_inst)

        self.boxdrawpanel = SimpleImagePanel(self, self.wximg)
        self.boxdrawpanel.box = roi

        self.boxdrawpanel.rescale(250)

        btn_ok = wx.Button(self, label="Use this region")
        btn_ok.Bind(wx.EVT_BUTTON, self.onButton_ok)
        btn_ok.Disable() # Can only click if the user draws a box.
        self.btn_ok = btn_ok

        btn_cancel = wx.Button(self, label="Cancel")
        btn_cancel.Bind(wx.EVT_BUTTON, self.onButton_cancel)
        
        btn_zoomin = wx.Button(self, label="Zoom In")
        btn_zoomin.Bind(wx.EVT_BUTTON, self.onButton_zoomin)
        btn_zoomout = wx.Button(self, label="Zoom Out")
        btn_zoomout.Bind(wx.EVT_BUTTON, self.onButton_zoomout)

        btn_sizer = wx.BoxSizer(wx.HORIZONTAL)
        btn_sizer.AddMany([(btn_ok,), ((20,0),), (btn_cancel,),
                           ((40,0,),),
                           (btn_zoomin,), ((20,0),), (btn_zoomout,)])

        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.sizer.Add(stxt_inst, flag=wx.CENTER)
        self.sizer.Add(self.boxdrawpanel, proportion=1, flag=wx.EXPAND | wx.CENTER)
        
        self.sizer.Add(btn_sizer, flag=wx.CENTER)

        self.SetSizer(self.sizer)
        self.Layout()

    def onButton_ok(self, evt):
        if not self.roi:
            wx.MessageDialog(self, message="Please select a region.").ShowModal()
            return
        self.roi = list(self.roi)
        self.roi[0] = max(self.roi[0] / self.boxdrawpanel.scale, 0)
        self.roi[1] = max(self.roi[1] / self.boxdrawpanel.scale, 0)
        self.roi[2] = min(self.roi[2] / self.boxdrawpanel.scale, self.npimg.shape[1])
        self.roi[3] = min(self.roi[3] / self.boxdrawpanel.scale, self.npimg.shape[0])
        self.roi = [int(round(coord)) for coord in self.roi]
        self.EndModal(wx.OK)
    def onButton_cancel(self, evt):
        self.roi = None
        self.EndModal(wx.CANCEL)
    def onButton_zoomin(self, evt):
        self.boxdrawpanel.zoomin()
    def onButton_zoomout(self, evt):
        self.boxdrawpanel.zoomout()

class SimpleImagePanel(ScrolledPanel):
    def __init__(self, parent, wximg, *args, **kwargs):
        ScrolledPanel.__init__(self, parent, *args, **kwargs)
        self.wximg = wximg
        self.wximg_orig = wximg

        self.isCreating = False
        self.isMoving = False
        # list BOX_IP: [int x1, y1, x2, y2], the 'in-progress' box.
        self.box_ip = None
        
        # list BOX: [int ul_x, ul_y, lr_x, lr_y]
        self.box = None

        self.scale = 1.0

        self.Bind(wx.EVT_PAINT, self.onPaint)
        self.Bind(wx.EVT_LEFT_DOWN, self.onLeftDown)
        self.Bind(wx.EVT_LEFT_UP, self.onLeftUp)
        self.Bind(wx.EVT_MOTION, self.onMotion)

        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.sizer.Add((wximg.GetWidth(), wximg.GetHeight()))

        self.SetSizer(self.sizer)
        self.Layout()
        self.SetupScrolling()

    def zoomin(self, amt=0.25):
        scale = self.scale + amt
        w_new = int(round(self.wximg_orig.GetWidth() * scale))
        self.rescale(w_new)
    def zoomout(self, amt=0.25):
        scale = self.scale - amt
        w_new = int(round(self.wximg_orig.GetWidth() * scale))
        self.rescale(w_new)

    def rescale(self, w_new):
        """ Rescale displayed image s.t. the image has width W_NEW.
        Maintains aspect ratio.
        """
        if self.wximg.GetWidth() == w_new:
            return
        npimg = util.wxImage2np(self.wximg_orig)
        h_new = int(round(npimg.shape[0] / (npimg.shape[1] / float(w_new))))
        if w_new <= 5 or h_new <= 5: # Don't downsize too much
            return
        self.scale = w_new / float(self.wximg_orig.GetWidth())
        npimg_resize = scipy.misc.imresize(npimg, (h_new, w_new), interp='bicubic')
        wximg_resize = wx.ImageFromBuffer(w_new, h_new, npimg_resize)
        w_old, h_old = self.wximg.GetWidth(), self.wximg.GetHeight()
        self.wximg = wximg_resize

        if self.box:
            # Rescale box
            fac = w_old / float(w_new)
            self.box = [int(round(coord / fac)) for coord in self.box]

        self.sizer.Detach(0)
        self.sizer.Add((w_new, h_new))
        self.Layout()
        self.SetupScrolling()
        self.Refresh()

    def onPaint(self, evt):
        if self.IsDoubleBuffered():
            dc = wx.PaintDC(self)
        else:
            dc = wx.BufferedPaintDC(self)
        self.PrepareDC(dc)
        dc.DrawBitmap(wx.BitmapFromImage(self.wximg), 0, 0)

        def draw_box(box, color="BLACK", thick=3):
            dc.SetBrush(wx.TRANSPARENT_BRUSH)
            dc.SetPen(wx.Pen(color, thick))
            x1, y1, x2, y2 = canonicalize_box(box)
            dc.DrawRectangle(x1, y1, abs(x2-x1), abs(y2-y1))
            
        if self.box:
            draw_box(self.box, color="BLUE", thick=3)
        if self.box_ip:
            draw_box(self.box_ip, color="RED", thick=3)

    def onLeftDown(self, evt):
        x, y = self.CalcUnscrolledPosition(evt.GetPositionTuple())
        if self.box:
            self.box = None
        self.box_ip = [x, y, x+1, y+1]
        
        self.isCreating = True
        self.Refresh()

    def onLeftUp(self, evt):
        x, y = self.CalcUnscrolledPosition(evt.GetPositionTuple())
        if not self.isCreating:
            return
        self.box_ip[2], self.box_ip[3] = max(min(x, self.wximg.GetWidth()), 0), max(min(y, self.wximg.GetHeight()), 0)
        self.box = canonicalize_box(self.box_ip)
        self.box_ip = None
        self.isCreating = False
        self.Refresh()
        self.GetParent().roi = self.box
        self.GetParent().btn_ok.Enable()

    def onMotion(self, evt):
        x, y = self.CalcUnscrolledPosition(evt.GetPositionTuple())
        if not self.isCreating:
            return
        self.box_ip[2], self.box_ip[3] = max(min(x, self.wximg.GetWidth()), 0), max(min(y, self.wximg.GetHeight()), 0)
        self.Refresh()

def gray2rgb_np(npimg):
    """ Convert a grayscale nparray image to an RGB nparray image. """
    if len(npimg.shape) == 3:
        return npimg
    npimg_rgb = np.zeros((npimg.shape[0], npimg.shape[1], 3), dtype=npimg.dtype)
    npimg_rgb[:,:,0] = npimg
    npimg_rgb[:,:,1] = npimg
    npimg_rgb[:,:,2] = npimg
    return npimg_rgb

class TM_Thread(threading.Thread):

    def __init__(self, queue, job_id, patch, img, imgpaths, tm_param,
                 win_ballot, win_target,
                 callback, *args, **kwargs):
        """
        Input:
            PATCH: An IplImage.
        """
        threading.Thread.__init__(self, *args, **kwargs)
        self.queue = queue
        self.job_id = job_id
        self.patch = patch
        self.img = img
        self.imgpaths = imgpaths
        self.tm_param = tm_param
        self.win_ballot = win_ballot
        self.win_target = win_target
        self.callback = callback
    def run(self):
        print "...running template matching..."
        t = time.time()
        #patch_str = self.patch.tostring()
        w, h = cv.GetSize(self.patch)
        # results: {str imgpath: [(x,y,score_i), ...]}
        #results = partask.do_partask(do_find_matches, self.imgpaths, 
        #                             _args=(patch_str, w, h, self.tm_param, self.win_ballot),
        #                             combfn='dict', singleproc=False)
        xwinB, ywinB = self.win_ballot
        xwinT, ywinT = self.win_target
        # results: {str imgpath: [(x1,y1,x2,y2,score_i), ...]}
        # Note: self.patch is already smooth'd.

        results = tempmatch.get_tempmatches_par(self.patch, self.imgpaths,
                                                do_smooth=tempmatch.SMOOTH_IMG_BRD,
                                                T=self.tm_param, xwinA=xwinT, ywinA=ywinT,
                                                xwinI=xwinB, ywinI=ywinB,
                                                jobid=self.job_id)

        dur = time.time() - t
        print "...finished running template matching ({0} s).".format(dur)
        wx.CallAfter(self.callback, results, w, h)

class Box(object):
    # SHADING: (int R, int G, int B)
    #     (Optional) color of transparent shading for drawing
    shading_clr = None
    shading_selected_clr = None

    shading_clr_cycle = None

    def __init__(self, x1, y1, x2, y2):
        self.x1, self.y1, self.x2, self.y2 = x1, y1, x2, y2
        self._dirty = True
    @property
    def width(self):
        return abs(self.x1-self.x2)
    @property
    def height(self):
        return abs(self.y1-self.y2)
    def __str__(self):
        return "Box({0},{1},{2},{3})".format(self.x1, self.y1, self.x2, self.y2)
    def __repr__(self):
        return "Box({0},{1},{2},{3})".format(self.x1, self.y1, self.x2, self.y2)
    def __eq__(self, o):
        return (isinstance(o, Box) and self.x1 == o.x1 and self.x2 == o.x2
                and self.y1 == o.y1 and self.y2 == o.y2)
    def canonicalize(self):
        """ Re-arranges my points (x1,y1),(x2,y2) such that we get:
            (x_upperleft, y_upperleft, x_lowerright, y_lowerright)
        """
        xa, ya, xb, yb = self.x1, self.y1, self.x2, self.y2
        w, h = abs(xa - xb), abs(ya - yb)
        if xa < xb and ya < yb:
            # UpperLeft, LowerRight
            self.x1, self.y1 = xa, ya
            self.x2, self.y2 = xb, yb
        elif xa < xb and ya > yb:
            # LowerLeft, UpperRight
            self.x1, self.y1 = xa, ya - h,
            self.x2, self.y2 = xb, yb + h
        elif xa > xb and ya < yb:
            # UpperRight, LowerLeft
            self.x1, self.y1 = xa - w, ya
            self.x2, self.y2 = xb + w, yb
        else:
            # LowerRight, UpperLeft
            self.x1, self.y1 = xb, yb
            self.x2, self.y2 = xa, ya
        return self
    def scale(self, scale):
        self.x1 = int(round(self.x1*scale))
        self.y1 = int(round(self.y1*scale))
        self.x2 = int(round(self.x2*scale))
        self.y2 = int(round(self.y2*scale))
    def copy(self):
        return Box(self.x1, self.y1, self.x2, self.y2)
    def get_draw_opts(self):
        """ Given the state of me, return the color+line-width for the
        DC to use.
        """
        return ("Green", 2)
    def marshall(self):
        return {'x1': self.x1, 'y1': self.y1, 'x2': self.x2, 'y2': self.y2}

class TargetBox(Box):
    shading_clr = (0, 255, 0) # Green
    shading_selected_clr = (255, 0, 0) # Red

    shading_clr_cycle = None

    def __init__(self, x1, y1, x2, y2, is_sel=False):
        Box.__init__(self, x1, y1, x2, y2)
        self.is_sel = is_sel
    def __str__(self):
        return "TargetBox({0},{1},{2},{3},is_sel={4})".format(self.x1, self.y1, self.x2, self.y2, self.is_sel)
    def __repr__(self):
        return "TargetBox({0},{1},{2},{3},is_sel={4})".format(self.x1, self.y1, self.x2, self.y2, self.is_sel)
    def get_draw_opts(self):
        """ Given the state of me, return the color+line-width for the
        DC to use.
        """
        if self.is_sel:
            return ("Yellow", 1)
        else:
            return ("Green", 1)
    def copy(self):
        return TargetBox(self.x1, self.y1, self.x2, self.y2, is_sel=self.is_sel)
class ContestBox(Box):
    shading_clr = (0, 0, 200) # Blue
    shading_selected_clr = (171, 0, 240) # Purple

    # shading_clr_cycle := A list of colors to alternate from
    shading_clr_cycle = ((0, 0, 200), (100, 0, 0), (0, 150, 245), (0, 230, 150), (100, 0, 190))

    def __init__(self, x1, y1, x2, y2, is_sel=False):
        Box.__init__(self, x1, y1, x2, y2)
        self.is_sel = is_sel
        self.colour = None

    def __str__(self):
        return "ContestBox({0},{1},{2},{3},is_sel={4})".format(self.x1, self.y1, self.x2, self.y2, self.is_sel)
    def __repr__(self):
        return "ContestBox({0},{1},{2},{3},is_sel={4})".format(self.x1, self.y1, self.x2, self.y2, self.is_sel)
    def get_draw_opts(self):
        """ Given the state of me, return the color+line-width for the
        DC to use.
        """
        if self.is_sel:
            return ("Yellow", 1)
        else:
            return ("Blue", 1)
    def copy(self):
        return ContestBox(self.x1, self.y1, self.x2, self.y2, is_sel=self.is_sel)
    
class SelectionBox(Box):
    def __str__(self):
        return "SelectionBox({0},{1},{2},{3})".format(self.x1, self.y1, self.x2, self.y2)
    def __repr__(self):
        return "SelectionBox({0},{1},{2},{3})".format(self.x1, self.y1, self.x2, self.y2)
    def get_draw_opts(self):
        return ("Black", 1)
    def copy(self):
        return SelectionBox(self.x1, self.y1, self.x2, self.y2)

def canonicalize_box(box):
    """ Takes two arbitrary (x,y) points and re-arranges them
    such that we get:
        (x_upperleft, y_upperleft, x_lowerright, y_lowerright)
    """
    xa, ya, xb, yb = box
    w, h = abs(xa - xb), abs(ya - yb)
    if xa < xb and ya < yb:
        # UpperLeft, LowerRight
        return (xa, ya, xb, yb)
    elif xa < xb and ya > yb:
        # LowerLeft, UpperRight
        return (xa, ya - h, xb, yb + h)
    elif xa > xb and ya < yb:
        # UpperRight, LowerLeft
        return (xa - w, ya, xb + w, yb)
    else:
        # LowerRight, UpperLeft
        return (xb, yb, xa, ya)

def get_boxes_within(boxes, box):
    """ Returns all boxes in BOXES that lie within BOX.
    Input:
        list boxes: [Box_i, ...]
        Box box: Enclosing box.
    Output:
        list outboxes.
    """
    result = []
    for boxA in boxes:
        wA, hA = int(abs(boxA.x1-boxA.x2)), int(abs(boxA.y1-boxA.y2))
        if (((boxA.x1+(wA/3)) >= box.x1) and
            ((boxA.x2-(wA/3)) <= box.x2) and
            ((boxA.y1+(hA/3)) >= box.y1) and
            ((boxA.y2-(hA/3)) <= box.y2)):
            result.append(boxA)
    return result

def expand_box(box, factor, bounds=None):
    """ Expands the Box BOX by FACTOR in each dimension. If BOUNDS is
    given, then this dictates the maximum (width,height) allowed.
    Input:
        Box BOX:
        float FACTOR: If 0.0, same size. 0.5 is 50% bigger, etc.
        list BOUNDS: (w,h)
    Output:
        Box OUTBOX.
    """
    b = box.copy()
    b.x1 = int(round(max(0, box.x1 - (box.width*factor))))
    b.y1 = int(round(max(0, box.y1 - (box.height*factor))))
    if bounds != None:
        b.x2 = int(round(min(bounds[0]-1, box.x2 + (box.width*factor))))
        b.y2 = int(round(min(bounds[1]-1, box.y2 + (box.height*factor))))
    else:
        b.x2 = int(round(box.x2 + (box.width*factor)))
        b.y2 = int(round(box.y2 + (box.height*factor)))
    return b

def compute_box_ids(boxes):
    """ Given a list of Boxes, some of which are Targets, others
    of which are Contests, geometrically compute the correct
    target->contest associations. Also outputs all voting targets
    which are not contained in a contest.
    Input:
        list BOXES:
    Output:
        (ASSOCS, LONELY_TARGETS)
    dict ASSOCS: {int contest_id, [ContestBox, [TargetBox_i, ...]]}
    list LONELY_TARGETS: [TargetBox_i, ...]
    """
    def containing_box(box, boxes):
        """ Returns the box in BOXES that contains BOX. """
        w, h = box.width, box.height
        # Allow some slack when checking which targets are contained by a contest
        slack_fact = 0.1
        xEps = int(round(w*slack_fact))
        yEps = int(round(h*slack_fact))
        for i, otherbox in enumerate(boxes):
            if ((box.x1+xEps) >= otherbox.x1 and (box.y1+yEps) >= otherbox.y1
                    and (box.x2-xEps) <= otherbox.x2 and (box.y2-yEps) <= otherbox.y2):
                return i, otherbox
        return None, None
    assocs = {}
    contests = [b for b in boxes if isinstance(b, ContestBox)]
    #print contests
    targets = [b for b in boxes if isinstance(b, TargetBox)]
    lonely_targets = []
    # Ensure that each contest C is present in output ASSOCS, even if
    # it has no contained voting targets
    # Note: output contest ids are determined by ordering in the CONTESTS list
    for contestid, c in enumerate(contests):
        assocs[contestid] = (c, [])

    for t in targets:
        id, c = containing_box(t, contests)
        if id == None:
            #print "Warning", t, "is not contained in any box."
            lonely_targets.append(t)
        elif id in assocs:
            assocs[id][1].append(t)
        else:
            assocs[id] = [c, [t]]
    return assocs, lonely_targets

def recolour_contests(contests):
    """ Performs a five-colouring on CONTESTS to improve UI experience.
    Input:
        list CONTESTS: [ContestBox_i, ...]
    Output:
        None. Mutates the input contests.
    """
    def contests2graph():
        contest2node = {} # maps {ContestBox: Node}
        node2contest = {} # maps {Node: ContestBox}
        for i, contest in enumerate(contests):
            node = graphcolour.Node((contest.x1,contest.y1, contest.x2, contest.y2, id(contest)))
            contest2node[contest] = node
            node2contest[node] = contest
        for i, contest0 in enumerate(contests):
            for j, contest1 in enumerate(contests):
                if i == j: continue
                if is_adjacent(contest0, contest1):
                    contest2node[contest0].add_neighbor(contest2node[contest1])
        return graphcolour.AdjListGraph(contest2node.values()), node2contest

    graph, node2contest = contests2graph()
    colouring = graphcolour.fivecolour_planar(graph, colours=ContestBox.shading_clr_cycle)
    if not colouring:
        print "Graph isn't planar, that's odd! Running general colouring algo..."
        colouring = graphcolour.graphcolour(graph, colours=ContestBox.shading_clr_cycle)
    for node, colour in colouring.iteritems():
        cbox = node2contest[node]
        cbox.colour = colour

def is_line_overlap_horiz(a, b):
    left = a if a[0] <= b[0] else b
    right = a if a[0] > b[0] else b
    if (left[0] < right[0] and left[1] < right[0]):
        return False
    return True
def is_line_overlap_vert(a, b):
    top = a if a[0] <= b[0] else b
    bottom = a if a[0] > b[0] else b
    if (top[0] < bottom[0] and top[1] < bottom[0]):
        return False
    return True

def is_adjacent(contest0, contest1, C=0.2):
    """ Returns True if the input ContestBoxes are adjacent. """
    def check_topbot(top, bottom):
        return (abs(top.y2 - bottom.y1) < thresh_h and 
                is_line_overlap_horiz((top.x1, top.x2), (bottom.x1, bottom.x2)))

    def check_leftright(left, right):
        return (abs(left.x2 - right.x1) < thresh_w and
                is_line_overlap_vert((left.y1,left.y2), (right.y1,right.y2)))
    thresh_w = C * min(contest0.width, contest1.width)
    thresh_h = C * min(contest0.height, contest1.height)
    left = contest0 if contest0.x1 <= contest1.x1 else contest1
    right = contest0 if contest0.x1 > contest1.x1 else contest1
    top = left if left.y1 <= right.y1 else right
    bottom = left if left.y1 > right.y1 else right

    if check_topbot(top, bottom):
        return True
    elif check_leftright(left, right):
        return True
    return False

def test_recolour_contests():
    A = ContestBox(50, 50, 75, 100)
    B = ContestBox(77, 48, 117, 102)
    C = ContestBox(200, 50, 250, 100)
    D = ContestBox(51, 100, 76, 121)

    contests = [A, B, C, D]
    recolour_contests(contests)
    for contest in contests:
        print "Contest ({0},{1}) Colour: {2}".format(contest.x1, contest.y1, contest.colour)
    pdb.set_trace()

"""
=======================
==== Sanity Checks ====
=======================
"""

# There are absolutely /no/ voting targets
ID_FLAG_NO_TARGETS = 0
_MSG_NO_TARGETS = "Error: No voting targets have been created yet. You \
will not be able to proceed until you select the voting targets."

# There are images that have no voting targets
ID_FLAG_EMPTY_IMAGES = 1

# There are images with only one voting target
ID_FLAG_ONLYONE_TARGET = 2

# There are voting targets not within a contest
ID_FLAG_LONELY_TARGETS = 3

# There are no contests defined
ID_FLAG_NO_CONTESTS = 4
_MSG_NO_CONTESTS = "Error: No contests have been created. You must define \
contests to proceed. The easiest way to define the contests is to click \
the Infer Contest Regions button; this automatically tries to detect the \
contest boundaries. Alternatively, if for some reason you need to do it \
entirely manually (which is much more work), you can click the Add Contest \
button and draw a rectangle around each individual contest."

# There are contests with no voting targets contained
ID_FLAG_EMPTY_CONTESTS = 5

# There are contests with only one voting target
ID_FLAG_CONTEST_ONE_TARGET = 6

def check_all_images_have_targets(boxes_map, flagged_idxs):
    """
    Input:
        dict BOXES_MAP: {int grp_idx: [[Box_i_side0, Box_i+1_side0, ...], [Box_i_side1, ...], ...]}
        set FLAGGED_IDXS: set([int idx, ...])
            Stores which grp_idxs in BOXES_MAP were flagged-to-be-quarantined
            by the user.
    Output:
        [(bool isOk_i, bool isFatal_i, str msg_i, int ID_FLAG, obj data), ...]
    """
    PASS, NOTPASS = True, False
    FATAL, NOTFATAL = True, False
    out_lst = []
    grp_contestcnts = util.Counter() # maps {(grp_idx, side): int contest_cnt}
    grp_targetcnts = util.Counter() # maps {(grp_idx, side): int target_cnt}
    grp_notargs = [] # [(int grp_idx, int side), ...]
    grp_nocontests = [] # [(int grp_idx, int side), ...]
    grp_onlyone_targ = [] # [(int grp_idx, int side), ...]
    lonely_targets_map = {} # maps {(int grp_idx, int side): [TargetBox_i, ...]}}
    cnt_lonely_targets = 0
    grp_contests_one_target = {} # maps {(int grp_idx, int side): [ContestBox_i, ...]}
    grp_empty_contests = {} # maps {(int grp_idx, int side): [ContestBox_i, ...]}
    for grp_idx, boxes_tups in boxes_map.iteritems():
        if grp_idx in flagged_idxs:
            continue
        for side, boxes in enumerate(boxes_tups):
            box_assocs, lonely_targets = compute_box_ids(boxes)
            cnt_lonely_targets += len(lonely_targets)
            if lonely_targets:
                lonely_targets_map.setdefault((grp_idx, side), []).extend(lonely_targets)
            targets = [b for b in boxes if isinstance(b, TargetBox)]
            contests = [b for b in boxes if isinstance(b, ContestBox)]
            grp_targetcnts[(grp_idx, side)] += len(targets)
            grp_contestcnts[(grp_idx, side)] += len(contests)
            if not targets:
                grp_notargs.append((grp_idx, side))
            if not contests:
                grp_nocontests.append((grp_idx, side))
            if len(targets) == 1:
                grp_onlyone_targ.append((grp_idx, side))
            
            for contestid, contest_tup in box_assocs.iteritems():
                contestbox, contest_targets = contest_tup[0], contest_tup[1]
                if len(contest_targets) == 0:
                    grp_empty_contests.setdefault((grp_idx, side), []).append(contestbox)
                elif len(contest_targets) == 1:
                    grp_contests_one_target.setdefault((grp_idx, side), []).append(contestbox)

    isok_notargets = sum(grp_targetcnts.values()) > 0
    isok_nocontests = sum(grp_contestcnts.values()) > 0
    out_lst.append((isok_notargets, True, _MSG_NO_TARGETS, ID_FLAG_NO_TARGETS, None))

    if not isok_notargets:
        return out_lst

    out_lst.append((isok_nocontests, True, _MSG_NO_CONTESTS, ID_FLAG_NO_CONTESTS, None))
    if not isok_nocontests:
        return out_lst
 
    if grp_notargs:
        msg_empty_images = "Warning: {0} different ballot images did not have \
any voting targets detected. If this is a mistake, please go back and \
correct it. \n\
Otherwise, if these images in fact do not contain any voting \
targets (e.g. they are blank), you may continue.".format(len(grp_notargs))
        out_lst.append((NOTPASS, NOTFATAL, msg_empty_images, ID_FLAG_EMPTY_IMAGES, grp_notargs))
    else:
        out_lst.append((PASS, NOTFATAL, "Pass", ID_FLAG_EMPTY_IMAGES, None))
    
    if grp_onlyone_targ:
        msg_onlyone_targ = "Warning: {0} ballot images only had one \
voting target detected. If this is a mistake, please bo back and correct \
the images.".format(len(grp_onlyone_targ))
        out_lst.append((NOTPASS, NOTFATAL, msg_onlyone_targ, ID_FLAG_ONLYONE_TARGET, grp_onlyone_targ))
    else:
        out_lst.append((PASS, NOTFATAL, "Pass", ID_FLAG_ONLYONE_TARGET, None))

    if cnt_lonely_targets > 0:
        msg_lonelytargets = "Warning: There were {0} targets that were \
not enclosed within a contest.".format(cnt_lonely_targets)
        out_lst.append((NOTPASS, FATAL, msg_lonelytargets, ID_FLAG_LONELY_TARGETS, lonely_targets_map))
    else:
        out_lst.append((PASS, FATAL, "Pass", ID_FLAG_LONELY_TARGETS, None))

    if grp_empty_contests:
        msg_emptycontests = "Warning: There were {0} contests that had \
no voting targets enclosed.".format(len(grp_empty_contests))
        out_lst.append((NOTPASS, NOTFATAL, msg_emptycontests, ID_FLAG_EMPTY_CONTESTS, grp_empty_contests))
    else:
        out_lst.append((PASS, NOTFATAL, "Pass", ID_FLAG_EMPTY_CONTESTS, None))
        
    if grp_contests_one_target:
        msg_contests_one_target = "Warning: There were {0} contests that \
had only one voting target.".format(len(grp_contests_one_target))
        out_lst.append((NOTPASS, FATAL, msg_contests_one_target, ID_FLAG_CONTEST_ONE_TARGET, grp_contests_one_target))
    else:
        out_lst.append((PASS, FATAL, "Pass", ID_FLAG_CONTEST_ONE_TARGET, None))

    return out_lst

"""
===========================
==== END Sanity Checks ====
===========================
"""

def img_to_wxbitmap(img, size=None):
    """ Converts IMG to a wxBitmap. """
    # TODO: Assumes that IMG is a wxImage
    if size:
        img_scaled = img.Scale(size[0], size[1], quality=wx.IMAGE_QUALITY_HIGH)
    else:
        img_scaled = img
    return wx.BitmapFromImage(img_scaled)
def pil2iplimage(img):
    """ Converts a (grayscale) PIL img IMG to a CV IplImage. """
    img_cv = cv.CreateImageHeader(map(int, img.size), cv.IPL_DEPTH_8U, 1)
    cv.SetData(img_cv, img.tostring())
    return img_cv
def iplimage2pil(img):
    """ Converts a (grayscale) CV IplImage to a PIL image. """
    return Image.fromstring("L", cv.GetSize(img), img.tostring())

def bestmatch(A, B):
    """ Tries to find the image A within the (larger) image B.
    For instance, A could be a voting target, and B could be a
    contest.
    Input:
        IplImage A: Patch to search for
        IplImage B: Image to search over
    Output:
        ((x,y), s_mat),  location on B of the best match for A.
    """
    w_A, h_A = A.width, A.height
    w_B, h_B = B.width, B.height
    s_mat = cv.CreateMat(h_B - h_A + 1, w_B - w_A + 1, cv.CV_32F)
    cv.MatchTemplate(B, A, s_mat, cv.CV_TM_CCOEFF_NORMED)
    minResp, maxResp, minLoc, maxLoc = cv.MinMaxLoc(s_mat)
    return maxLoc, s_mat

def align_partitions(partitions, (outrootdir, img2flip), queue=None, result_queue=None):
    """ 
    Input:
        list PARTITIONS: [[partitionID, [Ballot_i, ...]], [partitionID, [Ballot_i, ...]], ...]
        str OUTROOTDIR: Rootdir to save aligned images to.
    Output:
        dict PARTITIONS_ALIGN: {int partitionID: [BALLOT_i, ...]}
    """
    # Global Alignment approach: Perform alignment on a smaller patch
    # near the center, then apply the discovered transformation H to
    # the entire image. Works better than working on the entire image.
    partitions_align = {} # maps {partitionID: [[imgpath_i, ...], ...]}
    t = time.time()
    print "...this process is aligning {0} ballots...".format(sum(map(lambda t: len(t[1]), partitions), 0))
    try:
        for idx, (partitionid, ballots) in enumerate(partitions):
            outdir = pathjoin(outrootdir, 'partition_{0}'.format(partitionid))
            try: os.makedirs(outdir)
            except: pass
            ballotRef = ballots[0]
            Irefs = []
            for side, imP in enumerate(ballotRef):
                I = shared.standardImread_v2(imP, flatten=True)
                if img2flip[imP]:
                    I = shared.fastFlip(I)
                Irefs.append((imP, I))
            # 0.) First, handle the reference Ballot
            curBallot = []
            for side, (Iref_imP, Iref) in enumerate(Irefs):
                outname = 'bal_{0}_side_{1}.png'.format(0, side)
                outpath = pathjoin(outdir, outname)
                scipy.misc.imsave(outpath, Iref)
                curBallot.append(outpath)
            partitions_align[partitionid] = [curBallot]
            # 1.) Now, align all other Ballots to BALLOTREF
            for i, ballot in enumerate(ballots[1:]):
                curBallot = []
                for side, imgpath in enumerate(ballot):
                    Iref_imgP, Iref = Irefs[side]
                    I = shared.standardImread_v2(imgpath, flatten=True)
                    if img2flip[imgpath]:
                        I = shared.fastFlip(I)
                    H, Ireg, err = global_align.align_image(I, Iref)
                    outname = 'bal_{0}_side_{1}.png'.format(i + 1, side)
                    outpath = pathjoin(outdir, outname)
                    scipy.misc.imsave(outpath, Ireg)
                    curBallot.append(outpath)

                partitions_align[partitionid].append(curBallot)
            if queue:
                queue.put(True)
        dur = time.time() - t
        if result_queue:
            result_queue.put(partitions_align)
        return partitions_align
    except:
        traceback.print_exc()
        if result_queue:
            result_queue.put({})
        return None

def do_align_partitions(partitions, img2flip, outrootdir, manager, queue, N=None):
    """
    Input:
        list PARTITIONS[i][j][k] := i-th partition, j-th ballot, k-th side. 
        dict IMG2FLIP: maps {str imgpath: bool isflipped}
    Output:
        dict PARTITIONS_ALIGN. maps {int partitionID: [[imgpath_i, ...], ...]}
    """
    try:
        if N == None:
            N = min(multiprocessing.cpu_count(), len(partitions))
        # Evenly-distribute partitions by partition size.
        partitions_evenly = divy_lists(partitions, N)
        pool = multiprocessing.Pool()
        result_queue = manager.Queue()

        if N == 1:
            align_partitions(partitions_evenly[0], (outrootdir, img2flip), queue, result_queue)
        else:
            for i,task in enumerate(partitions_evenly):
                # TASK := [[partitionID, [Ballot_i, ...]], [partitionID, [Ballot_i, ...]], ...]
                pool.apply_async(align_partitions, args=(task, (outrootdir, img2flip), 
                                                         queue, result_queue))
            pool.close()
            pool.join()

        cnt = 0; num_tasks = len(partitions_evenly)
        partitions_align = {} 
        while cnt < num_tasks:
            subresult = result_queue.get()
            print '...got result {0}...'.format(cnt)
            partitions_align = dict(partitions_align.items() + subresult.items())
            cnt += 1
        return partitions_align
    except:
        traceback.print_exc()
        return None

def divy_lists(lst, N):
    """ Given a list of sublists (where each sublist may be of unequal
    size), output N lists of list of sublists, where the size of each 
    list of sublists is maximized (i.e. ensuring an equal distribution
    of sublist sizes).
    Input:
        list LST[i][j] := j-th element of i-th sublist
    Output:
        list OUT[i][j][k] := k-th element of j-th sublist within i-th list.
    """
    if len(lst) <= N:
        return [[[i, l]] for i, l in enumerate(lst)]
    outlst = [None]*N
    lst_np = np.array(lst)
    lstlens = map(lambda l: -len(l), lst_np)
    lstlens_argsort = np.argsort(lstlens)
    for i, lst_idx in enumerate(lstlens_argsort):
        sublist = lst[lst_idx]
        out_idx = i % N
        if outlst[out_idx] == None:
            outlst[out_idx] = [[lst_idx, sublist]]
        else:
            outlst[out_idx].append([lst_idx, sublist])
    return outlst

# TODO: Reference the util.py versions of the following conversion methods
def wxImage2np(Iwx, is_rgb=True):
    """ Converts wxImage to numpy array """
    w, h = Iwx.GetSize()
    Inp_flat = np.frombuffer(Iwx.GetDataBuffer(), dtype='uint8')
    if is_rgb:
        Inp = Inp_flat.reshape(h,w,3)
    else:
        Inp = Inp_flat.reshape(h,w)
    return Inp
def wxBitmap2np(wxBmp, is_rgb=True):
    """ Converts wxBitmap to numpy array """
    total_t = time.time()

    t = time.time() 
    Iwx = wxBmp.ConvertToImage()
    dur_bmp2wximg = time.time() - t
    
    t = time.time()
    npimg = wxImage2np(Iwx, is_rgb=True)
    dur_wximg2np = time.time() - t
    

    total_dur = time.time() - total_t
    print "==== wxBitmap2np: {0:.6f}s (bmp2wximg: {1:.5f}s {2:.3f}%) \
(wximg2np: {3:.5f}s {4:.3f}%)".format(total_dur,
                                      dur_bmp2wximg,
                                      100*(dur_bmp2wximg / total_dur),
                                      dur_wximg2np,
                                      100*(dur_wximg2np / total_dur))
    return npimg
def wxBitmap2np_v2(wxBmp, is_rgb=True):
    """ Converts wxBitmap to numpy array """
    total_t = time.time()
    
    w, h = wxBmp.GetSize()

    npimg = np.zeros(h*w*3, dtype='uint8')
    wxBmp.CopyToBuffer(npimg, format=wx.BitmapBufferFormat_RGB)
    npimg = npimg.reshape(h,w,3)

    total_dur = time.time() - total_t
    #print "==== wxBitmap2np_v2: {0:.6f}s".format(total_dur)
    return npimg
    
def isimgext(f):
    return os.path.splitext(f)[1].lower() in ('.png', '.bmp', 'jpeg', '.jpg', '.tif')

def distL2(x1,y1,x2,y2):
    return math.sqrt((float(y1)-y2)**2.0 + (float(x1)-x2)**2.0)

def main():
    class TestFrame(wx.Frame):
        def __init__(self, parent, partitions, *args, **kwargs):
            wx.Frame.__init__(self, parent, size=(800, 900), *args, **kwargs)
            self.parent = parent
            self.partitions = partitions

            self.st_panel = SelectTargetsPanel(self)
            self.st_panel.start(partitions)

    args = sys.argv[1:]
    imgsdir = args[0]
    try:
        mode = args[1]
    except:
        mode = 'single'
    partitions = []
    for dirpath, _, filenames in os.walk(imgsdir):
        partition = []
        imgpaths = [f for f in filenames if isimgext(f)]
        if mode == 'single':
            for imgname in [f for f in filenames if isimgext(f)]:
                partition.append([os.path.join(dirpath, imgname)])
        else:
            imgpaths = util.sorted_nicely(imgpaths)
            for i, imgname in enumerate(imgpaths[:-1:2]):
                page1 = os.path.join(dirpath, imgname)
                page2 = os.path.join(dirpath, imgpaths[i+1])
                partition.append([page1, page2])
        if partition:
            partitions.append(partition)
    app = wx.App(False)
    f = TestFrame(None, partitions)
    f.Show()
    app.MainLoop()

if __name__ == '__main__':
    #main()
    test_recolour_contests()
