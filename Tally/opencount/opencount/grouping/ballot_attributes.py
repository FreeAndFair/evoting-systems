import os, sys, threading, multiprocessing, shutil, pdb, time, random
try:
    import cPickle as pickle
except:
    import pickle
from Queue import Empty
from os.path import join as pathjoin

import wx, cv
from wx.lib.pubsub import Publisher
from wx.lib.scrolledpanel import ScrolledPanel

sys.path.append('..')
import util, tempmatch, group_attrs, common, config
import specify_voting_targets.select_targets as select_targets
import grouping.cust_attrs as cust_attrs
from panel_opencount import OpenCountPanel
from grouping.verify_overlays_new import CheckImageEqualsFrame, CheckImageEquals
"""
A widget that integrates the functionality of 'Define Attributes' and
'Select Attributes' into a unified UI component. The workflow is:

    Display an example ballot to the user. Ask the user how        (0)
    many attributes they would like to add. (Maybe not)

    Let B be set of unfinished ballots.
    Let C be set of completed ballots.

    Populate B with one ballot from each partition.                (0)
    while there are more ballots B to process:
        Display ballot B_i to the user.                            (1)
        The user draws a bounding box around an attribute A,       (2)
        and gives it a type+value (e.g. "Language", "English").

            Attribute Name:  Previous: <DROPDOWN> | Add new: <textEntry> <button '+'>
            Attribute Value: Previous: <DROPDOWN> | Add new: <textEntry> <button '+'>
            isDigitBased?
                number of digits:
            Consistent within a partition?
            For tabulation only?

        If A is digitBased, then don't do anything here - it will  (3)
        be handled in the current 'Label Digit Attributes" UI.
        If A is newly-created, then add all ballots from C to B.   (4)
            If A is not consistent within a partition, then        (4.a)
            add a subset of the ballots from each partition
            to B (e.g. 1000 ballots). 
    
        Search for instances of A across other ballots in B.       (5)
        The user verifies the matches via overlays.                (6)
        
        Action: User clicks 'Next'
            Remove B_i from B. Add B_i to C.

Note: The behavior of DigitBased attributes are a bit different.
The user only has to draw the attrbox for digit-based once. Then,
on each subsequent ballot, the digitbased attr boundingbox should
always be displayed.
"""

"""
TODO
1.) The "HAS_ANYBOX_CHANGED" functionality doesn't /quite/ work yet.
    It won't detect if a box's location has changed. But it /will/
    detect if a new box/attribute was created.
"""

# Fraction of ballots to add from each partition when considering a
# ballot attribute that varies within a partition.
GRP_MODE_ALL_BALLOTS_NUM = 0.2

GRP_MODE_ALL_BALLOTS_NUM_MIN = 10
GRP_MODE_ALL_BALLOTS_NUM_MAX = 150

JOBID_FIND_ATTR_MATCHES = util.GaugeID("FindAttrMatches")
JOBID_COMPUTE_MULT_EXEMPLARS = util.GaugeID("ComputeMultExemplars")

# ATTRMODES: Used for proj.attrprops {str ATTRMODE: dict PROPS}
ATTRMODE_IMG = "IMGBASED"
ATTRMODE_DIGIT = "DIGITBASED"
ATTRMODE_CUSTOM = "CUSTATTR"

OVERLAY_EXEMPLAR_IMGNAME = '_exemplar_patch.png'

class BallotAttributesPanel(OpenCountPanel):
    def __init__(self, *args, **kwargs):
        OpenCountPanel.__init__(self, *args, **kwargs)
        
        self.init_ui()
        
    def init_ui(self):
        self.attr_panel = DefineAttributesPanel(self)
        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.sizer.Add(self.attr_panel, proportion=1, flag=wx.EXPAND)
        self.SetSizer(self.sizer)
        self.Layout()
        
    def start(self, proj, stateP, *args, **kwargs):
        self.proj = proj
        self.attr_panel.start(proj, stateP)
        self.proj.addCloseEvent(self.attr_panel.save_session)
    def stop(self):
        self.proj.removeCloseEvent(self.attr_panel.save_session)
        self.attr_panel.save_session()
        self.export_results()
    def export_results(self):
        pass

    def invoke_sanity_checks(self, *args, **kwargs):
        """ Code that actually calls each sanity-check with application
        specific arguments. Outputs a list of statuses, like:

            [(bool isOk, bool isFatal, str msg, int id_flag, obj data), ...]
        """
        ID_IS_DONE = 0
        if self.attr_panel.am_i_done():
            return [(True, True, "", ID_IS_DONE, None)]
        else:
            msg = "Please finish annotating all ballot attributes. If \
you are on the last ballot, please click the 'Next' button one more time."
            return [(False, True, msg, ID_IS_DONE, None)]

class DefineAttributesPanel(ScrolledPanel):
    def __init__(self, parent, *args, **kwargs):
        ScrolledPanel.__init__(self, parent, *args, **kwargs)

        # self.BALLOTS_TODO: list [int ballotid_i, ...]
        self.ballots_todo = None
        # self.BALLOTS_COMPLETED: list [int ballotid_i, ...]
        self.ballots_completed = None

        self.bal2imgs = None
        self.img2bal = None
        self.img2page = None
        self.img2flip = None
        self.part2bal = None
        self.bal2part = None
        
        # dict BOXES_MAP: {int ballotID: [AttrBox_i, ...]}
        self.boxes_map = None

        # dict ATTRTYPES_MAP: {str attrtype: [AttrBox_i, ...]}
        #     Keeps track of each possible AttrBox value for each attrtype.
        self.attrtypes_map = None

        # self.CUST_ATTRS: [obj CustomAttribute_i, ...]
        self.cust_attrs = None
        # self.DIGIT_ATTRS: [obj AttrBox_i, ...]
        self.digit_attrs = None

        # dict PATCH2BAL: {str patchpath: (int ballotid, attrtype, attrval)}
        self.patch2bal = None
        # dict BAL2PATCHES: {int ballotid: ((patchpath, attrtype, attrval), ...)}
        self.bal2patches = None

        # CUR_SIDE: Which side we're displaying
        self.cur_side = 0
        # CUR_BALLOTID: Which ballot we are displaying.
        self.cur_ballotid = 0

        # TM_THRESHOLD: Minimum template-matching response required
        self.tm_threshold = 0.9

        # bool HAS_ANYBOX_CHANGED: If a user reviews ballot attribute
        # annotations, and he/she hasn't changed anything, then we 
        # shouldn't re-run multiple attribute exemplar computation.
        # This is the only usecase for this so far.
        self.HAS_ANYBOX_CHANGED = False

        self.stateP = None

        self.init_ui()
    
    def init_ui(self):
        self.toolbar = ToolBar(self)
        self.boxdraw = DrawAttrBoxPanel(self)
        self.footer = MyFooter(self)
        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.sizer.Add(self.toolbar)
        self.sizer.Add(self.boxdraw, proportion=1, flag=wx.EXPAND)
        self.sizer.Add(self.footer)

        self.SetSizer(self.sizer)
        self.Layout()
        self.SetupScrolling()

    def start(self, proj, stateP):
        self.proj = proj
        self.stateP = stateP
        self.img2page = pickle.load(open(pathjoin(proj.projdir_path,
                                                  proj.image_to_page), 'rb'))
        self.img2flip = pickle.load(open(pathjoin(proj.projdir_path,
                                                  proj.image_to_flip), 'rb'))
        self.bal2imgs = pickle.load(open(proj.ballot_to_images, 'rb'))
        self.img2bal = pickle.load(open(proj.image_to_ballot, 'rb'))
        self.part2bals = pickle.load(open(pathjoin(proj.projdir_path,
                                                   proj.partitions_map), 'rb'))
        self.bal2part = pickle.load(open(pathjoin(proj.projdir_path,
                                                  proj.partitions_invmap), 'rb'))
        
        if not self.restore_session():
            self.ballots_todo = []
            self.ballots_completed = []
            partition_exmpls = pickle.load(open(pathjoin(proj.projdir_path,
                                                         proj.partition_exmpls), 'rb'))
            for partitionID, ballotids in partition_exmpls.iteritems():
                self.ballots_todo.append(ballotids[0])
                
            self.boxes_map = {}
            self.cust_attrs = []
            self.digit_attrs = []
            self.attrtypes_map = {}
            self.patch2bal = {}
            self.bal2patches = {}
        else:
            if not self.ballots_todo:
                status = util.WarningDialog(self, "All ballots have already been annotated.\n\n\
Would you like to review the ballot annotations?",
                                            ("Yes, Review All Ballot Annotations", "No, Take Me To The Next Step"),
                                            (wx.ID_YES, wx.ID_NO)).ShowModal()
                if status == wx.ID_NO:
                    self.Disable()
                    return
                else:
                    self.repopulate_todo_list()
        self.cur_ballotid = self.ballots_todo[0]
        self.cur_side = 0
        self.display_image(self.cur_side, self.cur_ballotid)

    def repopulate_todo_list(self):
        """ Adds all ballots from self.ballots_completed to self.ballots_todo. """
        while self.ballots_completed:
            self.ballots_todo.append(self.ballots_completed.pop())

    def stop(self):
        self.export_results()
        self.Disable()

    def export_results(self):
        """ Populates the following data structures:
        ==== 'Define Attributes' stuff:

        list proj.ballot_attributesfile: [dict attrbox_marsh_i, ...]
            Only needs one AttrBox for each attrtype (ignores attrvals)
        dict proj.attrprops: {str ATTRMODE: {str attrtype: dict PROPS}}
            where ATTRMODE in ('DIGITBASED', 'IMGBASED', 'CUSTATTR')
            and PROPS has keys: 'attrtype', 'x1','y1','x2','y2', 'is_tabulationonly',
                                'side', 'grp_per_partition', 'num_digits'
        
        ==== 'Label Attributes' stuff:
        
        dict proj.partition_attrmap: {int partitionid: ([imgpath,x1,y1,w,h,attrtype,attrval,side,isdigitbased,istabonly], ...)}
        dict proj.multexemplars_map: {str attrtype: {str attrval: [(subpatchpath, votedpath, (x1,y1,x2,y2)), ...]}}
            subpatchP := This should point to the exemplar patch itself
            blankpathP := Points to the (entire) voted image that subpatchP came from
            (x1,y1,x2,y2) := BB that, from blankpathP, created subpatchP
        
        imgs proj.attrexemplars_dir:
            Save each exemplar imgpatch for each (attrtype,attrval) to disk.
        """
        ballot_attrs = [] # [dict attrbox_marsh, ...]
        attrprops = {} # {str ATTRMODE: dict PROPS}
        attrprops[ATTRMODE_IMG] = {}
        attrprops[ATTRMODE_DIGIT] = {}
        attrprops[ATTRMODE_CUSTOM] = {}

        ballot_attrs = [attrboxes[0].marshall() for attrboxes in self.attrtypes_map.values()]
        for attrtype, attrboxes in self.attrtypes_map.iteritems():
            attrbox_exmpl = attrboxes[0]
            props = {'attrtype': attrtype,
                     'x1': attrbox_exmpl.x1, 'y1': attrbox_exmpl.y1,
                     'x2': attrbox_exmpl.x2, 'y2': attrbox_exmpl.y2,
                     'is_tabulationonly': attrbox_exmpl.is_tabulationonly,
                     'side': attrbox_exmpl.side,
                     'grp_per_partition': attrbox_exmpl.grp_per_partition}
            if attrbox_exmpl.is_digitbased:
                props['num_digits'] = attrbox_exmpl.num_digits
                attrprops.setdefault(ATTRMODE_DIGIT, {})[attrtype] = props
            else:
                attrprops.setdefault(ATTRMODE_IMG, {})[attrtype] = props
        for cattr in self.cust_attrs:
            attrtype = cattr.attrname
            attrprops.setdefault(ATTRMODE_CUSTOM, {})[attrtype] = cattr.marshall()
        
        pickle.dump(ballot_attrs, open(self.proj.ballot_attributesfile, 'wb'))
        pickle.dump(attrprops, open(pathjoin(self.proj.projdir_path,
                                             self.proj.attrprops), 'wb'))

        partition_attrmap = {} # {int partID: ([imP,x1,y1,w,h,attrtype,attrval,side,isdigitbased,istabonly],...)}
        
        for ballotid, attrboxes in self.boxes_map.iteritems():
            partitionid = self.bal2part[ballotid]
            imgpaths = sorted(self.bal2imgs[ballotid], key=lambda imP: self.img2page[imP])
            attrs_list = []
            for box in attrboxes:
                attrtype = '_'.join(sorted(box.attrtypes))
                attrval = '_'.join(sorted(box.attrvals))
                imP = imgpaths[box.side]
                stuff = (imP, box.x1, box.y1, int(round(box.x2-box.x1)), int(round(box.y2-box.y1)),
                         attrtype, attrval, box.side, box.is_digitbased, box.is_tabulationonly)
                attrs_list.append(stuff)
            partition_attrmap.setdefault(partitionid, []).extend(attrs_list)
            
        pickle.dump(partition_attrmap, open(pathjoin(self.proj.projdir_path,
                                                     self.proj.partition_attrmap), 'wb'))

        if (self.HAS_ANYBOX_CHANGED or not os.path.exists(pathjoin(self.proj.projdir_path,
                                                                   self.proj.multexemplars_map))):
            manager = multiprocessing.Manager()
            queue = manager.Queue()
            tlisten = ThreadListener(queue, JOBID_COMPUTE_MULT_EXEMPLARS)
            tlisten.start()
            if config.TIMER:
                config.TIMER.start_task("BallotAttributes_ComputeMultExemplars_CPU")
            t = ThreadComputeMultExemplars(self.proj, self.boxes_map, self.bal2imgs, self.img2page,
                                           self.patch2bal, self.bal2patches, attrprops,
                                           queue, JOBID_COMPUTE_MULT_EXEMPLARS,
                                           self.on_compute_mult_exemplars_done, tlisten)
            t.start()
            num_tasks = len(self.attrtypes_map) # Num. attrs
            gauge = util.MyGauge(self, 1, thread=t, msg="Computing Multiple Exemplars...",
                                 job_id=JOBID_COMPUTE_MULT_EXEMPLARS)
            gauge.Show()
            wx.CallAfter(Publisher().sendMessage, "signals.MyGauge.nextjob", (num_tasks, JOBID_COMPUTE_MULT_EXEMPLARS))
        else:
            self.on_compute_mult_exemplars_done(None)
    def on_compute_mult_exemplars_done(self, multexemplars_map):
        if config.TIMER:
            config.TIMER.stop_task("BallotAttributes_ComputeMultExemplars_CPU")
        if multexemplars_map != None:
            pickle.dump(multexemplars_map, open(pathjoin(self.proj.projdir_path,
                                                         self.proj.multexemplars_map), 'wb'))
        wx.MessageDialog(self, style=wx.OK,
                         message="You may move onto the next step.").ShowModal()

    def restore_session(self):
        try:
            state = pickle.load(open(self.stateP, 'rb'))
            ballots_todo = state['ballots_todo']
            ballots_completed = state['ballots_completed']
            boxes_map = state['boxes_map']
            cust_attrs = state['cust_attrs']
            digit_attrs = state['digit_attrs']
            attrtypes_map = state['attrtypes_map']
            patch2bal = state['patch2bal']
            bal2patches = state['bal2patches']
            # Only set my properties if all entries are present.
            self.ballots_todo = ballots_todo
            self.ballots_completed = ballots_completed
            self.boxes_map = boxes_map
            self.cust_attrs = cust_attrs
            self.digit_attrs = digit_attrs
            self.attrtypes_map = attrtypes_map
            self.patch2bal = patch2bal
            self.bal2patches = bal2patches
        except:
            return False
        return True
    def save_session(self):
        # 0.) Add new changes from self.BOXDRAW to self.BOXES_MAP, if any
        self.boxes_map[self.cur_ballotid] = self.boxdraw.boxes
        state = {'boxes_map': self.boxes_map,
                 'cust_attrs': self.cust_attrs,
                 'digit_attrs': self.digit_attrs,
                 'ballots_todo': self.ballots_todo,
                 'ballots_completed': self.ballots_completed,
                 'attrtypes_map': self.attrtypes_map,
                 'patch2bal': self.patch2bal,
                 'bal2patches': self.bal2patches}
        pickle.dump(state, open(self.stateP, 'wb'), pickle.HIGHEST_PROTOCOL)

    def display_image(self, cur_side, cur_ballotid, autofit=True):
        """ Displays the CUR_SIDE-side of ballot CUR_BALLOTID.
        Input:
            int CUR_SIDE: 
            int CUR_BALLOTID:
            bool AUTOFIT
                If True, then this will autoscale the image such that
                if fits snugly in the current viewport.
        """
        if cur_side < 0 or cur_ballotid not in self.ballots_todo:
            return None

        imgpaths = sorted(self.bal2imgs[cur_ballotid], key=lambda imP: self.img2page[imP])
        
        if cur_side >= len(imgpaths):
            return None

        self.cur_side = cur_side
        self.cur_ballotid = cur_ballotid

        imgpath = imgpaths[cur_side]
        boxes = [b for b in self.boxes_map.get(cur_ballotid, []) if b.side == self.cur_side]
        wximg = wx.Image(imgpath, wx.BITMAP_TYPE_ANY)
        if self.img2flip[imgpath]:
            wximg = wximg.Rotate90().Rotate90()
        if autofit:
            wP, hP = self.boxdraw.GetClientSize()
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
            size = (w_img_new, h_img_new)
        else:
            size = None
        self.boxdraw.set_image(wximg, size=size)
        self.boxdraw.set_boxes(boxes)
        self.update_ui_text()
        self.Refresh()
        self.boxdraw.Refresh()
    
    def get_attrtypes(self):
        """ Returns a list of all attrtypes currently created so far,
        excluding custom attributes.
        """
        return list(self.attrtypes_map.keys())
    
    def add_custom_attr(self, cattr_box):
        """ Adds the customattribute CATTR_BOX to my data structs.
        Input:
            obj CATTR_BOX: A CustomAttribute instance
        """
        if cattr_box not in self.cust_attrs:
            self.cust_attrs.append(cattr_box)
        return self.cust_attrs

    def register_attr(self, attrbox):
        """ Modifies relevant data structures to be aware of the newly
        created ATTRBOX.
        """
        attrtype = '_'.join(sorted(attrbox.attrtypes))
        attrval = '_'.join(sorted(attrbox.attrvals))
        if attrtype not in self.attrtypes_map:
            is_new_attrtype = True
            self.attrtypes_map[attrtype] = [attrbox]
        else:
            is_new_attrtype = False
            self.attrtypes_map[attrtype].append(attrbox)
        return is_new_attrtype

    def enforce_attrbox_consistency(self, box, MATCH_NEW=False):
        """ If the newly-created box BOX's attrtype already
        exists in self.attrtypes_map, but any attribute is different
        (i.e. is_digitbased, num_digits, is_tabulationonly, side, grp_per_partition),
        then modify all the other previously-created AttrBoxes so
        that it matches this one, to avoid discrepancies.
        If MATCH_NEW is True, then we modify the previously-created
        boxes. Else, modify the newly created box.
        """
        def update_box(box_prev, box_new, properties):
            box_to_change = box_prev if MATCH_NEW else box_new
            box_to_match = box_prev if not MATCH_NEW else box_new
            for prop in properties:
                if getattr(box_prev, prop) != getattr(box_new, prop):
                    wx.MessageDialog(self, message="Changing property! {0} from {1} to {2}".format(prop,
                                                                                                   getattr(box_prev, prop),
                                                                                                   getattr(box_new, prop))).ShowModal()
                    setattr(box_to_change, prop, getattr(box_to_match, prop))

        attrtype = "_".join(sorted(box.attrtypes))
        attrboxes_prev = self.attrtypes_map.get(attrtype, ())
        relevant_props = ("is_digitbased", "num_digits", "is_tabulationonly",
                          "side", "grp_per_partition")
        for box_prev in attrboxes_prev:
            update_box(box_prev, box, relevant_props)

    def handle_usermade_attrbox(self, attrbox):
        """ Given a newly-created AttributeBox ATTRBOX, does the relevant
        logic/computation/updates according to our spec.
        Input:
            AttrBox ATTRBOX:
            dict BOXES_MAP: {int ballotid: [AttrBox_i, ...]}
            list BALLOTS_TODO: [int ballotid_i, ...]
            list BALLOTS_COMPLETED: [int ballotid_i, ...]
        Output:
            (dict BOXES_MAP, list BALLOTS_TODO, list BALLOTS_COMPLETED).
        Returns (possibly) updated versions of BOXES_MAP, BALLOTS_TODO,
        BALLOTS_COMPLETED.
        """
        self.HAS_ANYBOX_CHANGED = True
        self.enforce_attrbox_consistency(attrbox)

        is_new_attrtype = self.register_attr(attrbox)
        if attrbox.is_digitbased:
            # Add this attrbox to /all/ ballots
            for ballotid in self.ballots_todo:
                self.boxes_map.setdefault(ballotid, []).append(attrbox.copy())
            for ballotid in self.ballots_completed:
                self.boxes_map.setdefault(ballotid, []).append(attrbox.copy())
            # We also want to add this attrbox to all future ballotids, so
            # record digitbased attributes in separate data struct
            self.digit_attrs.append(attrbox)
            return
        if is_new_attrtype:
            self.ballots_todo.extend(list(self.ballots_completed))
            self.ballots_completed[:] = [] # clears the list
            if not attrbox.grp_per_partition:
                # Attr varies within each partition. Sample N ballots
                # to label from each partition.
                set_ballots_todo = set(self.ballots_todo)
                for partitionid, ballotids in self.part2bals.iteritems():
                    balids_candidates = [balid for balid in ballotids if balid not in set_ballots_todo]
                    if not balids_candidates:
                        continue
                    n = int(GRP_MODE_ALL_BALLOTS_NUM * len(balids_candidates))
                    n = max(min(n, GRP_MODE_ALL_BALLOTS_NUM_MAX), GRP_MODE_ALL_BALLOTS_NUM_MIN)
                    n = min(n, len(balids_candidates))
                    print "(Info) Sampling {0} ballots from this partition (out of {1})".format(n, len(ballotids))
                    ballotids_chosen = random.sample(balids_candidates, n)
                    for balid in ballotids_chosen:
                        self.ballots_todo.append(balid)
                        # Add in digit-based attrs!
                        for digitbox in self.digit_attrs:
                            self.boxes_map.setdefault(balid, []).append(digitbox.copy())
                    
        attrpatch_outdir = pathjoin(self.proj.projdir_path, 
                                    self.proj.extract_attrs_templates)
        # exemplar_imgpath: is actually saved in find_attr_matches()
        exemplar_imgpath = pathjoin(self.proj.projdir_path,
                                    OVERLAY_EXEMPLAR_IMGNAME)

        self.Disable()
        if config.TIMER:
            config.TIMER.start_task("BallotAttributes_FindAttrMatches_CPU")
        manager = multiprocessing.Manager()
        queue_mygauge = manager.Queue()
        jobid = JOBID_FIND_ATTR_MATCHES
        thread_listener = ThreadListener(queue_mygauge, jobid)
        thread_listener.start()
        thread = ThreadFindAttrMatches(self.ballots_todo, self.cur_ballotid, attrbox, attrpatch_outdir,
                                       self.proj.voteddir,
                                       self.bal2imgs,
                                       self.img2bal, self.img2flip, self.img2page,
                                       exemplar_imgpath,
                                       manager, queue_mygauge, jobid, thread_listener,
                                       self.on_findmatches_done)
        thread.start()

        num_tasks = len(self.ballots_todo)
        gauge = util.MyGauge(self, 1, msg="Finding Attribute Matches...",
                             thread=thread, job_id=jobid)
        gauge.Show()
        wx.CallAfter(Publisher().sendMessage, "signals.MyGauge.nextjob", (num_tasks, jobid))

    def on_findmatches_done(self, matches, patchpath2bal, attrbox):
        """ Invoked once the template-matching attribute matching is
        finished computing.
        Input:
            dict MATCHES: {int ballotid: ((x1, y1, x2, y2), float score, str patchpath)}
            dict PATCHPATH2BAL: {str patchpath: int ballotid}
            obj ATTRBOX:
        """
        if config.TIMER:
            config.TIMER.stop_task("BallotAttributes_FindAttrMatches_CPU")
        # Filter matches for only high-quality matches (w.r.t. self.tm_threshold)
        patchpaths_filtered = []
        patchpaths_bad = []
        for ballotid, (bb, score, patchpath) in matches.iteritems():
            if score >= self.tm_threshold:
                patchpaths_filtered.append(patchpath)
            else:
                patchpaths_bad.append(patchpath)

        # Remove bad imgpatches from disk (optional, but let's do it)
        for patchpath_bad in patchpaths_bad:
            os.remove(patchpath_bad)

        if config.TIMER:
            config.TIMER.start_task("BallotAttributes_VerifyMatches_H")
        callback = lambda verifyresults: self.on_verifymatches_done(verifyresults, matches, patchpath2bal, attrbox)
        exemplar_imgpath = pathjoin(self.proj.projdir_path,
                                    OVERLAY_EXEMPLAR_IMGNAME)
        f = CheckImageEqualsFrame(self, patchpaths_filtered, exemplar_imgpath, callback)
        self.f = f
        f.Show()
        f.Maximize()
        wx.CallAfter(f.Layout)

    def on_verifymatches_done(self, verifyresults, matches, patchpath2bal, attrbox):
        """ Invoked once the overlay verification is finished.
        Input:
            dict VERIFYRESULTS: {str tag: [patchpath_i, ...]}
            dict MATCHES: {int ballotid: ((x1,y1,x2,y2), float score, str patchpath)}
            dict PATCHPATH2BAL: {str patchpath: int ballotid}
            obj ATTRBOX:
        """
        if config.TIMER:
            config.TIMER.stop_task("BallotAttributes_VerifyMatches_H")
        self.f.Close()
        self.Enable()
        good_matches = verifyresults.get(CheckImageEquals.TAG_YES, ())
        attrtype = '_'.join(sorted(attrbox.attrtypes))
        attrval = '_'.join(sorted(attrbox.attrvals))
        print "...Number of 'good' matches for '{0}': {1}->{2}".format(len(good_matches), attrtype, attrval)

        def update_bal2patches(ballotid, patchP, attrtype, attrval, OP="add"):
            for ballotid, tups in self.bal2patches.iteritems():
                for i, (patchpath, atype, aval) in enumerate(tups)[::-1]:
                    if atype == attrtype:
                        tups.pop(i) # Pop from reverse iter to avoid bugs
                if OP == "add":
                    tups.append((patchP, attrtype, attrval))

        for patchpath in good_matches:
            ballotid = patchpath2bal[patchpath]
            self.patch2bal[patchpath] = (ballotid, attrtype, attrval)
            update_bal2patches(ballotid, patchpath, attrtype, attrval, OP="add")
            if attrbox not in self.boxes_map.get(ballotid, []):
                # This 'if' ensures we don't double-add attrbox to the
                # ballot that we drew the box on.
                self.boxes_map.setdefault(ballotid, []).append(attrbox)
            if (ballotid != self.cur_ballotid) and (len(self.boxes_map[ballotid]) == len(self.attrtypes_map)):
                # This ballot has annotated all attrtypes
                # Don't remove the currently-displayed ballot, in case
                # the user wants to add more attributes.
                self.ballots_todo.remove(ballotid)
                self.ballots_completed.append(ballotid)

        # Remove badmatch image patches from disk (optional, but let's do it)
        bad_matches = verifyresults.get(CheckImageEquals.TAG_NO, [])
        for patchpath in bad_matches:
            os.remove(patchpath)
            try: balid, atype, aval = self.patch2bal.pop(patchpath)
            except KeyError: balid, atype, aval = None, None, None
            if balid != None:
                update_bal2patches(balid, patchpath, atype, aval, OP="remove")
            
        self.update_ui_text()

    def mark_ballot_done(self, ballotid):
        """ Marks the ballot BALLOTID as done. Returns the next
        ballotid to show, or None if we're done.
        """
        self.ballots_todo.remove(ballotid)
        self.ballots_completed.append(ballotid)
        if len(self.ballots_todo) == 0:
            return None
        return self.ballots_todo[0]

    def am_i_done(self):
        """ Returns True if the user is done labeling all tasks. """
        return self.ballots_todo != None and len(self.ballots_todo) == 0
    def is_ballot_done(self, ballotid):
        """ The user is finished annotating this ballot if the number of
        attributes present is equal to the total number of non-digitbased
        attributes.
        """
        num_nondigitattrs = 0
        for attrtype, attrboxes in self.attrtypes_map.iteritems():
            if attrboxes and not attrboxes[0].is_digitbased:
                num_nondigitattrs += 1
        my_boxes = [b for b in self.boxes_map.get(ballotid, []) if not b.is_digitbased]
        return len(my_boxes) == num_nondigitattrs

    def update_ui_text(self):
        self.footer.stxt_num_bals.SetLabel("{0}.".format(len(self.ballots_todo)))
        self.footer.stxt_cur_page.SetLabel("{0}".format(self.cur_side+1))
        imgpaths = self.bal2imgs[self.cur_ballotid]
        self.footer.stxt_total_pages.SetLabel("{0}.".format(len(imgpaths)))
        self.Layout()
        self.Refresh()

    def mark_image_flipped(self, balid, side):
        """ Mark an image as flipped -- this will update the UI (if the 
        image in question is currently displayed), as well as
        update the image_to_flip data structure permanently, for all other
        OpenCount components to see.
        Input:
            int BALID: 
            int SIDE:
        """
        imgpaths_sorted = sorted(self.bal2imgs[balid], key=lambda imP: self.img2page[imP])
        imgpath = imgpaths_sorted[side]
        print "Setting img2flip for image '{0}' FROM '{1}' TO '{2}'".format(imgpath,
                                                                            self.img2flip[imgpath],
                                                                            not self.img2flip[imgpath])
        self.img2flip[imgpath] = not self.img2flip[imgpath]
        pickle.dump(self.img2flip, open(os.path.join(self.proj.projdir_path, self.proj.image_to_flip), 'wb'))
        if balid == self.cur_ballotid and side == self.cur_side:
            self.display_image(side, balid)

    def next_side(self):
        self.display_image(self.cur_side + 1, self.cur_ballotid)
    def prev_side(self):
        self.display_image(self.cur_side - 1, self.cur_ballotid)
    def next_img(self):
        self.boxes_map[self.cur_ballotid] = self.boxdraw.boxes
        if not self.is_ballot_done(self.cur_ballotid):
            wx.MessageDialog(self, message="Can't move on - please \
annotate other ballot attributes.", style=wx.OK).ShowModal()
            return
        next_ballotid = self.mark_ballot_done(self.cur_ballotid)
        if self.am_i_done():
            wx.MessageDialog(self, style=wx.OK,
                             message="All ballot attributes have been \
labeled - this step is now complete.\n\n\
Please move to the next step.").ShowModal()
            self.stop()
            return
        elif next_ballotid == None:
            wx.MessageDialog(self, style=wx.OK,
                             message="Unexpected: next_ballotid was None.").ShowModal()
            return
        else:
            self.display_image(0, next_ballotid)
    def prev_img(self):
        # Not sure what to do here...
        pass
    def mark_all_ballots_done(self):
        """ Marks all ballots as done -- if any ballot still has attributes
        to label, then this halt at that ballot(s) and tell the user to label
        them.
        """
        while self.ballots_todo:
            balid = self.ballots_todo[0]
            if not self.is_ballot_done(balid):
                wx.MessageDialog(self, style=wx.OK,
                                 message="There still exist ballots that \
lack attribute annotations. Please continue annotating those ballots.").ShowModal()
                self.display_image(0, balid)
                return
            else:
                balid = self.mark_ballot_done(balid)
                if self.am_i_done():
                    wx.MessageDialog(self, style=wx.OK,
                                     message="All ballot attributes have been \
labeled - this step is now complete.\n\n\
Please move to the next step.").ShowModal()
                    self.stop()
                    return

class ToolBar(wx.Panel):
    def __init__(self, parent, *args, **kwargs):
        wx.Panel.__init__(self, parent, *args, **kwargs)
        
        self.init_ui()

    def init_ui(self):
        btn_addattr = wx.Button(self, label="Add Attribute")
        btn_addattr.Bind(wx.EVT_BUTTON, self.onButton_addattr)
        btn_modify = wx.Button(self, label="Modify")
        btn_modify.Bind(wx.EVT_BUTTON, self.onButton_modify)
        btn_zoomin = wx.Button(self, label="Zoom In")
        btn_zoomin.Bind(wx.EVT_BUTTON, self.onButton_zoomin)
        btn_zoomout = wx.Button(self, label="Zoom Out")
        btn_zoomout.Bind(wx.EVT_BUTTON, self.onButton_zoomout)
        btn_addcustomattr = wx.Button(self, label="Add Custom Attribute...")
        btn_addcustomattr.Bind(wx.EVT_BUTTON, self.onButton_addcustomattr)
        btn_viewcustomattrs = wx.Button(self, label="View Custom Attributes...")
        btn_viewcustomattrs.Bind(wx.EVT_BUTTON, self.onButton_viewcustomattrs)
        btn_markflip = wx.Button(self, label="Mark As Flipped")
        btn_markflip.Bind(wx.EVT_BUTTON, self.onButton_markflip)
        btn_sizer = wx.BoxSizer(wx.HORIZONTAL)
        btn_sizer.AddMany([(btn_addattr,), (btn_modify,), (btn_addcustomattr,),
                           (btn_viewcustomattrs,), 
                           ((50,50),), 
                           (btn_zoomin,), (btn_zoomout,),
                           ((50,50),),
                           (btn_markflip,)])

        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.sizer.Add(btn_sizer)

        self.SetSizer(self.sizer)
        self.Layout()
    def onButton_zoomin(self, evt):
        self.GetParent().boxdraw.zoomin()
    def onButton_zoomout(self, evt):
        self.GetParent().boxdraw.zoomout()
    def onButton_addattr(self, evt):
        boxdrawpanel = self.GetParent().boxdraw
        boxdrawpanel.set_mode_m(boxdrawpanel.M_CREATE)
    def onButton_modify(self, evt):
        boxdrawpanel = self.GetParent().boxdraw
        boxdrawpanel.set_mode_m(boxdrawpanel.M_IDLE)
    def onButton_addcustomattr(self, evt):
        SPREADSHEET = 'SpreadSheet'
        FILENAME = 'Filename'
        choice_dlg = common.SingleChoiceDialog(self, message="Which modality \
will the Custom Attribute use?", 
                                               choices=[SPREADSHEET, FILENAME])
        status = choice_dlg.ShowModal()
        if status == wx.ID_CANCEL:
            return
        choice = choice_dlg.result
        if choice == None:
            return
        elif choice == SPREADSHEET:
            attrtypes = self.GetParent().get_attrtypes()
            if len(attrtypes) == 0:
                print "No attrtypes created yet, can't do this."
                d = wx.MessageDialog(self, message="You must first create \
    Ballot Attributes, before creating Custom Ballot Attributes.")
                d.ShowModal()
                return
            dlg = SpreadSheetAttrDialog(self, attrtypes)
            status = dlg.ShowModal()
            if status == wx.ID_CANCEL:
                return
            attrname = dlg.attrname
            spreadsheetpath = dlg.path
            attrin = dlg.attrtype_selected
            is_tabulationonly = dlg.is_tabulationonly
            if not attrname:
                d = wx.MessageDialog(self, message="You must choose a valid \
attribute name.")
                d.ShowModal()
                return
            elif not spreadsheetpath:
                d = wx.MessageDialog(self, message="You must choose the \
spreadsheet path.")
                d.ShowModal()
                return
            elif not attrin:
                d = wx.MessageDialog(self, message="You must choose an \
'input' attribute type.")
                d.ShowModal()
                return
            cattr = cust_attrs.Spreadsheet_Attr(attrname, spreadsheetpath, attrin,
                                                is_tabulationonly)
            self.GetParent().add_custom_attr(cattr)
        elif choice == FILENAME:
            print "Handling Filename-based Custom Attribute."
            dlg = FilenameAttrDialog(self)
            status = dlg.ShowModal()
            if status == wx.ID_CANCEL:
                return
            if dlg.regex == None:
                d = wx.MessageDialog(self, message="You must choose \
an input regex.")
                d.ShowModal()
                return
            elif dlg.attrname == None:
                d = wx.MessageDialog(self, message="You must choose \
an Attribute Name.")
                d.ShowModal()
                return
            attrname = dlg.attrname
            regex = dlg.regex
            is_tabulationonly = dlg.is_tabulationonly
            cattr = cust_attrs.Filename_Attr(attrname, regex, is_tabulationonly)
            self.GetParent().add_custom_attr(cattr)
        
    def onButton_viewcustomattrs(self, evt):
        proj = self.GetParent().GetParent().proj
        custom_attrs = self.GetParent().cust_attrs
        if not custom_attrs:
            d = wx.MessageDialog(self, message="No Custom Attributes yet.")
            d.ShowModal()
            return
        print "Custom Attributes are:"
        for cattr in custom_attrs:
            attrname = cattr.attrname
            if isinstance(cattr, cust_attrs.Spreadsheet_Attr):
                print "  Attrname: {0} SpreadSheet: {1} Attr_In: {2}".format(attrname,
                                                                             cattr.sspath,
                                                                             cattr.attrin)
            elif isinstance(cattr, cust_attrs.Filename_Attr):
                print "  Attrname: {0} FilenameRegex: {1}".format(attrname,
                                                                  cattr.filename_regex)

    def onButton_markflip(self, evt):
        status = wx.MessageDialog(self, style=wx.YES_NO,
                                  caption="Mark Image as Flipped?",
                                  message="Are you sure that you want to \
mark this image as being upside down (flipped)? This will affect future \
stages of the OpenCount pipeline.").ShowModal()
        if status != wx.ID_YES:
            return
        cur_ballot, cur_side = self.GetParent().cur_ballotid, self.GetParent().cur_side
        self.GetParent().mark_image_flipped(cur_ballot, cur_side)
class MyFooter(wx.Panel):
    def __init__(self, *args, **kwargs):
        wx.Panel.__init__(self, *args, **kwargs)
        self.init_ui()
        
    def init_ui(self):
        sizer_bals = wx.BoxSizer(wx.VERTICAL)

        sizer_bals_btns = wx.BoxSizer(wx.HORIZONTAL)
        btn_next_ballot = wx.Button(self, label="Next Ballot")
        btn_next_ballot.Bind(wx.EVT_BUTTON, self.onButton_nextBallot)
        btn_prev_ballot = wx.Button(self, label="Previous Ballot")
        btn_prev_ballot.Bind(wx.EVT_BUTTON, self.onButton_prevBallot)
        sizer_bals_btns.AddMany([(btn_next_ballot,), (btn_prev_ballot,)])
        
        sizer_num_bals = wx.BoxSizer(wx.HORIZONTAL)
        stxt_num_bals_info = wx.StaticText(self, label="Number of Ballots remaining: ")
        self.stxt_num_bals = wx.StaticText(self, label="")
        sizer_num_bals.AddMany([(stxt_num_bals_info,),
                                (self.stxt_num_bals,)])
        
        sizer_bals.Add(sizer_bals_btns, flag=wx.ALIGN_CENTER)
        sizer_bals.Add(sizer_num_bals, flag=wx.ALIGN_CENTER)

        sizer_pages = wx.BoxSizer(wx.VERTICAL)
        
        sizer_pages_btns = wx.BoxSizer(wx.HORIZONTAL)
        btn_next_page = wx.Button(self, label="Next Page")
        btn_next_page.Bind(wx.EVT_BUTTON, self.onButton_nextPage)
        btn_prev_page = wx.Button(self, label="Previous Page")
        btn_prev_page.Bind(wx.EVT_BUTTON, self.onButton_prevPage)
        sizer_pages_btns.AddMany([(btn_next_page,), (btn_prev_page,)])

        btn_mark_all_done = wx.Button(self, label="Mark All Ballots Done")
        btn_mark_all_done.Bind(wx.EVT_BUTTON, self.onButton_markAllBallotsDone)
        
        sizer_pages_txt = wx.BoxSizer(wx.HORIZONTAL)
        stxt_num_pages_info = wx.StaticText(self, label="Page: ")
        self.stxt_cur_page = wx.StaticText(self, label="")
        stxt_num_pages_slash = wx.StaticText(self, label=" / ")
        self.stxt_total_pages = wx.StaticText(self, label="")
        sizer_pages_txt.AddMany([(stxt_num_pages_info,),
                                 (self.stxt_cur_page,),
                                 (stxt_num_pages_slash,),
                                 (self.stxt_total_pages,)])
        sizer_pages.Add(sizer_pages_btns, flag=wx.ALIGN_CENTER)
        sizer_pages.Add(sizer_pages_txt, flag=wx.ALIGN_CENTER)
        
        self.sizer = wx.BoxSizer(wx.HORIZONTAL)

        self.sizer.AddMany([(sizer_bals,), (sizer_pages,), ((25,0),), (btn_mark_all_done,)])

        self.SetSizer(self.sizer)
        self.Layout()

    def onButton_nextBallot(self, evt):
        self.GetParent().next_img()
    def onButton_prevBallot(self, evt):
        self.GetParent().prev_img()
    def onButton_nextPage(self, evt):
        self.GetParent().next_side()
    def onButton_prevPage(self, evt):
        self.GetParent().prev_side()
    def onButton_markAllBallotsDone(self, evt):
        self.GetParent().mark_all_ballots_done()

class DrawAttrBoxPanel(select_targets.BoxDrawPanel):
    def __init__(self, parent, *args, **kwargs):
        select_targets.BoxDrawPanel.__init__(self, parent, *args, **kwargs)

    def onLeftDown(self, evt):
        self.SetFocus()
        x, y = self.CalcUnscrolledPosition(evt.GetPositionTuple())
        x_img, y_img = self.c2img(x,y)
        w_img, h_img = self.img.GetSize()
        if x_img >= (w_img-1) or y_img >= (h_img-1):
            return

        if self.mode_m == self.M_CREATE:
            print "...Creating Attr Box..."
            self.clear_selected()
            self.startBox(x, y, AttrBox)
        elif self.mode_m == self.M_IDLE:
            boxes = self.get_boxes_within(x, y, mode='any')
            if boxes:
                box = boxes[0][0]
                if box not in self.sel_boxes:
                    self.clear_selected()
                    self.select_boxes(boxes[0][0])
            else:
                self.clear_selected()
                self.startBox(x, y, select_targets.SelectionBox)
        else:
            self.clear_selected()
            self.dirty_all_boxes()
        self.Refresh()
    def onLeftUp(self, evt):
        x, y = self.CalcUnscrolledPosition(evt.GetPositionTuple())
        if self.mode_m == self.M_CREATE and self.isCreate:
            box = self.finishBox(x, y)
            dlg = AddAttributeDialog(self, box, self.GetParent().attrtypes_map)
            status = dlg.ShowModal()
            if status == wx.CANCEL:
                self.Refresh()
                return
            box.attrtypes = [dlg.attrtype_new]
            box.attrvals = [dlg.attrval_new]
            box.is_digitbased = dlg.is_digitbased
            box.num_digits = dlg.num_digits
            box.is_tabulationonly = dlg.is_tabulationonly
            box.side = self.GetParent().cur_side
            box.grp_per_partition = dlg.is_consistent_part
            label = ', '.join(box.attrtypes) + '->' + ', '.join(box.attrvals)
            if box.is_digitbased:
                label += ' (DigitBased)'
            if box.is_tabulationonly:
                label += ' (TabulationOnly)'
            box.label = label
            self.boxes.append(box)
            self.GetParent().handle_usermade_attrbox(box)
        elif self.mode_m == self.M_IDLE and self.isCreate:
            box = self.finishBox(x, y)
            boxes = select_targets.get_boxes_within(self.boxes, box)
            print "...Selecting {0} boxes.".format(len(boxes))
            self.select_boxes(*boxes)
        self.Refresh()

    def drawBoxes(self, boxes, dc):
        select_targets.BoxDrawPanel.drawBoxes(self, boxes, dc)
        for attrbox in [b for b in self.boxes if isinstance(b, AttrBox)]:
            dc.SetBrush(wx.TRANSPARENT_BRUSH)
            dc.SetTextForeground("Blue")
            w = int(round(abs(attrbox.x2 - attrbox.x1) * self.scale))
            h = int(round(abs(attrbox.y2 - attrbox.y1) * self.scale))
            client_x, client_y = self.img2c(attrbox.x1, attrbox.y1)
            w_txt, h_txt = dc.GetTextExtent(attrbox.label)
            x_txt, y_txt = client_x, client_y - h_txt
            if y_txt < 0:
                y_txt = client_y + h
            dc.DrawText(attrbox.label, x_txt, y_txt)

class AttrBox(select_targets.Box):
    shading_clr = (0, 255, 0)
    shading_selected_clr = (255, 0, 0)

    def __init__(self, x1, y1, x2, y2, is_sel=False, label='', attrtypes=None,
                 attrvals=None,
                 is_digitbased=None, num_digits=None, is_tabulationonly=None,
                 side=None, grp_per_partition=None):
        """
        Input:
            bool GRP_PER_PARTITION:
                If True, then this is an attribute that is consistent
                within a single partition P, where partitions are 
                defined by the barcode value(s).
        """
        select_targets.Box.__init__(self, x1, y1, x2, y2)
        self.is_sel = is_sel
        self.label = label
        # TODO: Assume that there is only one attrtype per AttrBox.
        # I don't think we'll ever need multiple attributes per bounding box.
        self.attrtypes = attrtypes
        self.attrvals = attrvals
        self.is_digitbased = is_digitbased
        self.num_digits = num_digits
        self.is_tabulationonly = is_tabulationonly
        self.side = side
        self.grp_per_partition = grp_per_partition
    def __str__(self):
        return "AttrBox({0},{1},{2},{3},{4})".format(self.x1, self.y1, self.x2, self.y2, self.label)
    def __repr__(self):
        return "AttrBox({0},{1},{2},{3},{4})".format(self.x1, self.y1, self.x2, self.y2, self.label)
    def __eq__(self, o):
        return (isinstance(o, AttrBox) and self.x1 == o.x1 and self.x2 == o.x2
                and self.y1 == o.y1 and self.y2 == o.y2 and self.label == o.label
                and self.side == o.side and self.attrvals == o.attrvals
                and self.attrtypes == o.attrtypes)
    def copy(self):
        return AttrBox(self.x1, self.y1, self.x2, self.y2, label=self.label,
                       attrtypes=self.attrtypes, attrvals=self.attrvals, 
                       is_digitbased=self.is_digitbased,
                       num_digits=self.num_digits, is_tabulationonly=self.is_tabulationonly,
                       side=self.side, grp_per_partition=self.grp_per_partition)
    def get_draw_opts(self):
        if self.is_sel:
            return ("Yellow", 3)
        else:
            return ("Green", 3)
    def marshall(self):
        """ Return a dict-equivalent version of myself. """
        data = select_targets.Box.marshall(self)
        data['attrs'] = self.attrtypes
        data['attrvals'] = self.attrvals
        data['side'] = self.side
        data['is_digitbased'] = self.is_digitbased
        data['num_digits'] = self.num_digits
        data['is_tabulationonly'] = self.is_tabulationonly
        data['grp_per_partition'] = self.grp_per_partition
        return data

class AddAttributeDialog(wx.Dialog):
    def __init__(self, parent, attrbox, attrtypes_map, *args, **kwargs):
        """
        Input:
            obj ATTRBOX:
                The newly-created attribute box.
            dict ATTRTYPES_MAP: {str attrtype: [AttrBox_i, ...]}
                The previously-created attribute boxes.
        """
        wx.Dialog.__init__(self, parent, style=wx.CAPTION | wx.RESIZE_BORDER | wx.MAXIMIZE_BOX | wx.MINIMIZE_BOX, *args, **kwargs)

        self.attrbox_cur = attrbox
        self.attrtypes_map = attrtypes_map

        # Outbound results
        self.attrtype_new = None
        self.attrval_new = None
        self.is_digitbased = None
        self.num_digits = None
        self.is_tabulationonly = None
        self.is_consistent_part = None

        self.init_ui()
        for attrtype in sorted(attrtypes_map.keys()):
            self.cbox_prev_attrtypes.Append(attrtype)

        if not attrtypes_map:
            # Auto-ask the first attrtype/attrval pair.
            isdigattr = self.onButton_attrtype_add(None)
            if not isdigattr:
                self.onButton_attrval_add(None)
        self.Refresh()
        self.Layout()
    
    def init_ui(self):
        sizer_attrtype = wx.BoxSizer(wx.HORIZONTAL)
        txt_attrtype_name = wx.StaticText(self, label="Attribute Type: ")
        txt_attrtype_prev = wx.StaticText(self, label="Previously-entered: ")
        self.cbox_prev_attrtypes = wx.ComboBox(self, style=wx.CB_READONLY)
        self.cbox_prev_attrtypes.Bind(wx.EVT_COMBOBOX, self.onCombo_prevAttrTypes)
        btn_attrtype_addnew = wx.Button(self, label="Add new Type...")
        btn_attrtype_addnew.Bind(wx.EVT_BUTTON, self.onButton_attrtype_add)
        
        sizer_attrtype.AddMany([(txt_attrtype_name, 0, wx.ALL, 10),
                                (txt_attrtype_prev,),
                                (self.cbox_prev_attrtypes,),
                                (btn_attrtype_addnew,)])
        
        sizer_attrval = wx.BoxSizer(wx.HORIZONTAL)
        txt_attrval = wx.StaticText(self, label="Attribute Value: ")
        txt_attrval_prev = wx.StaticText(self, label="Previously-entered: ")
        self.cbox_prev_attrvals = wx.ComboBox(self, style=wx.CB_READONLY)
        btn_attrval_addnew = wx.Button(self, label="Add new Value...")
        btn_attrval_addnew.Bind(wx.EVT_BUTTON, self.onButton_attrval_add)

        sizer_attrval.AddMany([(txt_attrval,),
                               (txt_attrval_prev,),
                               (self.cbox_prev_attrvals,),
                               (btn_attrval_addnew,)])

        sizer_digits = wx.BoxSizer(wx.VERTICAL)
        sizer_digits_isit = wx.BoxSizer(wx.HORIZONTAL)
        txt_isdigitbased = wx.StaticText(self, label="Is this a digit-based attribute? ")
        self.chk_isdigitbased = wx.CheckBox(self)
        self.chk_isdigitbased.Bind(wx.EVT_CHECKBOX, self.onCheckBox_isdigitbased)
        sizer_digits_isit.AddMany([(txt_isdigitbased,),
                                   (self.chk_isdigitbased,)])

        sizer_digits_numdigits = wx.BoxSizer(wx.HORIZONTAL)
        txt_numdigits = wx.StaticText(self, label="    Number of Digits: ")
        self.spinctrl_numdigits = wx.SpinCtrl(self)
        self.spinctrl_numdigits.Disable()
        sizer_digits_numdigits.AddMany([(txt_numdigits,),
                                        (self.spinctrl_numdigits,)])
        sizer_digits.AddMany([(sizer_digits_isit,),
                              (sizer_digits_numdigits,)])

        sizer_grp_mode = wx.BoxSizer(wx.HORIZONTAL)
        txt_isPartConsistent = wx.StaticText(self, label="Is this attribute \
consistent within each partition (as defined by the barcodes)?")
        self.chk_is_consistent_part = wx.CheckBox(self)
        sizer_grp_mode.AddMany([(txt_isPartConsistent,),
                                (self.chk_is_consistent_part,)])
        
        sizer_tabulationOnly = wx.BoxSizer(wx.HORIZONTAL)
        txt_tabOnly = wx.StaticText(self, label="Is this attribute \
for tabulation purposes only?")
        self.chk_isTabOnly = wx.CheckBox(self)
        sizer_tabulationOnly.AddMany([(txt_tabOnly,),
                                      (self.chk_isTabOnly,)])

        sizer_btns = wx.BoxSizer(wx.HORIZONTAL)
        btn_ok = wx.Button(self, label="Add this Attribute")
        btn_ok.Bind(wx.EVT_BUTTON, self.onButton_ok)
        btn_cancel = wx.Button(self, label="Cancel this Attribute")
        btn_cancel.Bind(wx.EVT_BUTTON, self.onButton_cancel)
        sizer_btns.AddMany([(btn_ok,),
                            (btn_cancel,)])

        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.sizer.Add(sizer_attrtype)
        self.sizer.Add(sizer_attrval)
        self.sizer.Add(sizer_digits)
        self.sizer.Add(sizer_grp_mode)
        self.sizer.Add(sizer_tabulationOnly)
        self.sizer.Add(sizer_btns, flag=wx.ALIGN_CENTER)

        self.SetSizer(self.sizer)
        self.Fit()

    def onCombo_prevAttrTypes(self, evt):
        """ User selected an attribute type from the dropdown. Populate a
        few Attrval-related UI widgets.
        """
        attrname = self.cbox_prev_attrtypes.GetValue()
        attrboxes = self.attrtypes_map[attrname]
        self.cbox_prev_attrvals.Clear()
        attrval_possibles = set()
        for attrbox in attrboxes:
            attrval = '_'.join(sorted(attrbox.attrvals))
            attrval_possibles.add(attrval)
        for attrval in sorted(tuple(attrval_possibles)):
            self.cbox_prev_attrvals.Append(attrval)
        self.chk_isdigitbased.SetValue(attrboxes[0].is_digitbased)
        if attrboxes[0].is_digitbased:
            self.spinctrl_numdigits.Enable()
            self.spinctrl_numdigits.SetValue(attrboxes[0].num_digits)
        else:
            self.spinctrl_numdigits.Disable()
        self.chk_isTabOnly.SetValue(attrboxes[0].is_tabulationonly)
        self.chk_is_consistent_part.SetValue(attrboxes[0].grp_per_partition)

    def onCheckBox_isdigitbased(self, evt):
        """ User checked the "Is Digit Based?" checkbox. """
        if self.chk_isdigitbased.GetValue():
            self.spinctrl_numdigits.Enable()
        else:
            self.spinctrl_numdigits.Disable()

    def onButton_attrtype_add(self, evt):
        class AttrtypeDialog(wx.Dialog):
            def __init__(self, parent, *args, **kwargs):
                wx.Dialog.__init__(self, parent, title="New Attribute Type", *args, **kwargs)

                self.attrname = None
                self.is_digit = None

                sizer_attrname = wx.BoxSizer(wx.HORIZONTAL)
                stxt_attrname = wx.StaticText(self, label="Please enter the \
name of the new attribute type.")
                self.txtctrl_attrname = wx.TextCtrl(self, size=(150,-1), style=wx.TE_PROCESS_ENTER)
                self.txtctrl_attrname.Bind(wx.EVT_TEXT_ENTER, self.onButton_ok)
                sizer_attrname.AddMany([(stxt_attrname, 0, wx.ALL, 10), (self.txtctrl_attrname, 0, wx.ALL, 10)])
                
                self.chkbox_isdigit = wx.CheckBox(self, label="Is this a digit attribute?")

                sizer_btns = wx.BoxSizer(wx.HORIZONTAL)
                btn_ok = wx.Button(self, label="Ok")
                btn_ok.Bind(wx.EVT_BUTTON, self.onButton_ok)
                btn_cancel = wx.Button(self, label="Cancel")
                btn_cancel.Bind(wx.EVT_BUTTON, lambda evt: self.EndModal(wx.ID_CANCEL))
                sizer_btns.AddMany([(btn_ok, 0, wx.ALL | wx.ALIGN_CENTER, 10), (btn_cancel, 0, wx.ALL | wx.ALIGN_CENTER, 10)])
                
                self.sizer = wx.BoxSizer(wx.VERTICAL)
                self.sizer.AddMany([(sizer_attrname, 0, wx.ALL, 5), (self.chkbox_isdigit, 0, wx.ALL, 5)])
                self.sizer.Add(sizer_btns, 0, flag=wx.ALL | wx.ALIGN_CENTER, border=5)

                self.SetSizer(self.sizer)
                self.Fit()
                self.txtctrl_attrname.SetFocus()
            def onButton_ok(self, evt):
                self.attrname = self.txtctrl_attrname.GetValue()
                self.is_digit = self.chkbox_isdigit.GetValue()
                self.EndModal(wx.ID_OK)
                
        dlg = wx.TextEntryDialog(self, message="Please enter the name of \
the new attribute type.", caption="New Attribute Type")
        dlg = AttrtypeDialog(self)
        status = dlg.ShowModal()
        if status == wx.ID_CANCEL:
            return
        attrtype_new = dlg.attrname
        if '_' in attrtype_new:
            wx.MessageDialog(self, message="Please don't include the \
following characters: _", style=wx.OK).ShowModal()
            return
        if attrtype_new not in self.cbox_prev_attrtypes.GetItems():
            self.cbox_prev_attrtypes.Append(attrtype_new)
        self.cbox_prev_attrtypes.SetStringSelection(attrtype_new)
        self.Layout()
        if dlg.is_digit:
            return True
        else:
            return False

    def onButton_attrval_add(self, evt):
        dlg = wx.TextEntryDialog(self, message="Please enter the name of \
the new attribute value.", caption="New Attribute Value")
        status = dlg.ShowModal()
        if status == wx.CANCEL:
            return
        attrval_new = dlg.GetValue()
        if '_' in attrval_new:
            wx.MessageDialog(self, message="Please don't include the \
following characters: _", style=wx.OK).ShowModal()
            return
        if attrval_new not in self.cbox_prev_attrvals.GetItems():
            self.cbox_prev_attrvals.Append(attrval_new)
        self.cbox_prev_attrvals.SetStringSelection(attrval_new)
        self.Layout()

    def onButton_ok(self, evt):
        # Do relevant value setting
        self.attrtype_new = self.cbox_prev_attrtypes.GetValue()
        self.attrval_new = self.cbox_prev_attrvals.GetValue()
        self.is_digitbased = self.chk_isdigitbased.GetValue()
        self.num_digits = int(self.spinctrl_numdigits.GetValue())
        self.is_tabulationonly = self.chk_isTabOnly.GetValue()
        self.is_consistent_part = self.chk_is_consistent_part.GetValue()

        if (not self.attrtype_new or (not self.is_digitbased and not self.attrval_new)):
            wx.MessageDialog(self, message="You must enter an attribute \
type and an attribute value!", style=wx.OK).ShowModal()
            return
        if (self.is_digitbased and self.num_digits == ''):
            wx.MessageDialog(self, message="Please enter the number of \
digits that this attribute has.", style=wx.OK).ShowModal()
            return
        
        self.EndModal(wx.OK)
    def onButton_cancel(self, evt):
        self.EndModal(wx.CANCEL)

class SpreadSheetAttrDialog(wx.Dialog):
    def __init__(self, parent, attrtypes, *args, **kwargs):
        wx.Dialog.__init__(self, parent, *args, **kwargs)

        self.attrname = None
        self.attrtype_selected = None
        # The path that the user selected
        self.path = ''
        self.is_tabulationonly = None

        self.attrtypes = attrtypes

        sizer_attrname = wx.BoxSizer(wx.HORIZONTAL)
        txt_attrname = wx.StaticText(self, label="New attribute name: ")
        self.attrname_inputctrl = wx.TextCtrl(self, size=(250,-1))
        sizer_attrname.AddMany([(txt_attrname,), (self.attrname_inputctrl,)])

        txt = wx.StaticText(self, label="Spreadsheet File:")
        file_inputctrl = wx.TextCtrl(self, style=wx.TE_READONLY)
        self.file_inputctrl = file_inputctrl
        btn_select = wx.Button(self, label="Select...")
        btn_select.Bind(wx.EVT_BUTTON, self.onButton_selectfile)

        sizer_horiz = wx.BoxSizer(wx.HORIZONTAL)
        txt2 = wx.StaticText(self, label="Custom attr is a 'function' of:")
        self.combobox = wx.ComboBox(self, choices=attrtypes, style=wx.CB_READONLY)
        sizer_horiz.Add(txt2)
        sizer_horiz.Add(self.combobox, proportion=1, flag=wx.EXPAND)

        self.chkbox_tabonly = wx.CheckBox(self, label="Is this tabulation only?")

        btn_sizer = wx.BoxSizer(wx.HORIZONTAL)
        btn_ok = wx.Button(self, label="Create This Attribute")
        btn_ok.Bind(wx.EVT_BUTTON, self.onButton_create)
        btn_cancel = wx.Button(self, label="Cancel")
        btn_cancel.Bind(wx.EVT_BUTTON, self.onButton_cancel)
        btn_sizer.AddMany([(btn_ok,), ((50,50),), (btn_cancel,)])

        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.sizer.Add(sizer_attrname)
        sizer_file = wx.BoxSizer(wx.HORIZONTAL)
        sizer_file.Add(txt)
        sizer_file.Add((10, 10))
        sizer_file.Add(file_inputctrl, proportion=1, flag=wx.EXPAND)
        sizer_file.Add(btn_select)
        self.sizer.Add(sizer_file)
        self.sizer.Add(sizer_horiz)
        self.sizer.Add((50,50))
        self.sizer.Add(self.chkbox_tabonly)
        self.sizer.Add((50,50))
        self.sizer.Add(btn_sizer, flag=wx.ALIGN_CENTER)

        self.SetSizer(self.sizer)
        self.Layout()

    def onButton_selectfile(self, evt):
        dlg = wx.FileDialog(self, message="Choose spreadsheet...",
                            defaultDir='.', style=wx.FD_OPEN)
        status = dlg.ShowModal()
        if status == wx.ID_CANCEL:
            return
        path = dlg.GetPath()
        self.file_inputctrl.SetValue(path)
    def onButton_create(self, evt):
        if not self.combobox.GetValue():
            wx.MessageDialog(self, message="Error: Please select an \
attribute first.", style=wx.OK).ShowModal()
            return
        if not self.file_inputctrl.GetValue():
            wx.MessageDialog(self, message="Error: Please select the \
spreadsheet file path first.", style=wx.OK).ShowModal()
            return
        self.attrname = self.attrname_inputctrl.GetValue()
        self.attrtype_selected = self.combobox.GetValue()
        self.path = self.file_inputctrl.GetValue()
        self.is_tabulationonly = self.chkbox_tabonly.GetValue()
        self.EndModal(wx.ID_OK)
    def onButton_cancel(self, evt):
        self.EndModal(wx.ID_CANCEL)

class FilenameAttrDialog(wx.Dialog):
    """
    Dialog that handles the creation of a Filename-based Custom
    Attribute. The user-input will be a regex-like expression in order
    to extract the 'attribute' from the filename. For instance, to 
    extract the last digit '0' from a filename like:
        329_141_250_145_0.png
    The user-input regex would be:
        r'\d*_\d*_\d*_\d*_(\d*).png'
    """
    def __init__(self, parent, *args, **kwargs):
        wx.Dialog.__init__(self, parent, *args, **kwargs)
        self.parent = parent
        
        # self.attrname is the name of the CustomAttribute
        self.attrname = None
        # self.regex is the user-inputted regex to use
        self.regex = None
        self.is_tabulationonly = False

        sizer = wx.BoxSizer(wx.VERTICAL)

        txt1 = wx.StaticText(self, label="Please enter a Python-style \
regex that will match the attribute value.")
        sizer.Add(txt1)
        sizer.Add((20, 20))

        sizer_input0 = wx.BoxSizer(wx.HORIZONTAL)
        txt0 = wx.StaticText(self, label="Custom Attribute Name:")
        attrname_input = wx.TextCtrl(self, style=wx.TE_PROCESS_ENTER)
        attrname_input.Bind(wx.EVT_TEXT_ENTER, lambda evt: re_input.SetFocus())
        self.attrname_input = attrname_input
        sizer_input0.Add(txt0)
        sizer_input0.Add(attrname_input, proportion=1, flag=wx.EXPAND)
        sizer.Add(sizer_input0, flag=wx.EXPAND)
        
        sizer.Add((20, 20))

        sizer_input = wx.BoxSizer(wx.HORIZONTAL)
        txt2 = wx.StaticText(self, label="Regex Pattern:")
        sizer_input.Add(txt2)
        re_input = wx.TextCtrl(self, value=r'\d*_\d*_\d*_\d*_(\d*).png',
                               style=wx.TE_PROCESS_ENTER)
        self.re_input = re_input
        re_input.Bind(wx.EVT_TEXT_ENTER, self.onButton_ok)
        sizer_input.Add(re_input, proportion=1, flag=wx.EXPAND)

        sizer.Add(sizer_input, proportion=1, flag=wx.EXPAND)

        self.is_tabulationonly_chkbox = wx.CheckBox(self, label="Is this \
for Tabulation Only?")
        sizer.Add(self.is_tabulationonly_chkbox)
        
        btn_sizer = wx.BoxSizer(wx.HORIZONTAL)
        btn_ok = wx.Button(self, label="Ok")
        btn_ok.Bind(wx.EVT_BUTTON, self.onButton_ok)
        btn_sizer.Add(btn_ok)
        btn_cancel = wx.Button(self, label="Cancel")
        btn_cancel.Bind(wx.EVT_BUTTON, self.onButton_cancel)
        btn_sizer.Add(btn_cancel)

        sizer.Add(btn_sizer, flag=wx.ALIGN_CENTER)
        self.SetSizer(sizer)
        self.Fit()

        self.attrname_input.SetFocus()
        
    def onButton_ok(self, evt):
        self.attrname = self.attrname_input.GetValue()
        self.regex = self.re_input.GetValue()
        self.is_tabulationonly = self.is_tabulationonly_chkbox.GetValue()
        self.EndModal(wx.ID_OK)

    def onButton_cancel(self, evt):
        self.EndModal(wx.ID_CANCEL)        

def find_attr_matches(ballots_todo, src_balid, attrbox, attrpatch_outdir, voteddir,
                      bal2imgs, img2bal, img2flip, img2page,
                      exemplar_outpath,
                      queue_mygauge, jobid, EXPAND=0.5):
    """ Does template matching for attribute ATTRBOX over ballots in
    BALLOTS_TODO. For performance, also extracts the patch paths to
    ATTRPATCH_OUTDIR.
    Input:
        list BALLOTS_TODO: [int ballotid_i, ...]
        int SRC_BALID:
            Ballotid that ATTRBOX came from.
        AttrBox ATTRBOX:
        str ATTRPATCH_OUTDIR:
        str VOTEDDIR:
        dict BAL2IMGS:
        dict IMG2BAL:
        dict IMG2FLIP:
        dict IMG2PAGE:
        str EXEMPLAR_OUTPATH:
            Path to save the selected imgpatch to, for usage as the
            exemplar image in CheckImageEquals.
        float EXPAND:
            How much to expand the search window by.
    Output:
        (dict MATCHES, dict patchpath2bal, AttrBox ATTRBOX).
    dict MATCHES: {int ballotid: ((x1, y1, x2, y2), float score, str patchpath)}
    dict PATCHPATH2BAL: {str patchpath: int ballotid}
    """
    imgpaths = sorted(bal2imgs[src_balid], key=lambda imP: img2page[imP])
    imgpath_curBal = imgpaths[attrbox.side]
    I = cv.LoadImage(imgpath_curBal, cv.CV_LOAD_IMAGE_GRAYSCALE)
    if img2flip[imgpath_curBal]:
        cv.Flip(I, I, -1)
    w, h = cv.GetSize(I)
    cv.SetImageROI(I, (attrbox.x1, attrbox.y1, attrbox.x2 - attrbox.x1, attrbox.y2 - attrbox.y1))
    w_attr, h_attr = cv.GetSize(I)

    attrtype = '_'.join(sorted(attrbox.attrtypes))
    attrval = '_'.join(sorted(attrbox.attrvals))

    cv.SaveImage(exemplar_outpath, I)
    
    imgpaths_toSearch = []
    for ballotid in ballots_todo:
        imgpaths = sorted(bal2imgs[ballotid], key=lambda imP: img2page[imP])
        imgpaths_toSearch.append(imgpaths[attrbox.side])

    bb_search = (max(0, int(round(attrbox.x1 - (EXPAND*w_attr)))),
                 max(0, int(round(attrbox.y1 - (EXPAND*h_attr)))),
                 min(w-1, int(round(attrbox.x2 + (EXPAND*w_attr)))),
                 min(h-1, int(round(attrbox.y2 + (EXPAND*h_attr)))))

    patch_outpaths = {} # maps {str imgpath: str patch_outpath}
    patchpath2bal = {} # maps {str patch_outpath: int ballotid}
    for imgpath in imgpaths_toSearch:
        rp = os.path.relpath(os.path.abspath(imgpath),
                             os.path.abspath(voteddir))
        outname = "{0}_{1}.png".format(attrtype, attrval)
        outpath = pathjoin(attrpatch_outdir, rp, outname)
        patch_outpaths[imgpath] = outpath
        patchpath2bal[outpath] = img2bal[imgpath]

    # dict TM_MATCHES: {str imgpath: (x1,y1, float response)}
    tm_matches = tempmatch.bestmatch_par(I, imgpaths_toSearch, img2flip=img2flip,
                                         bb=bb_search, do_smooth=tempmatch.SMOOTH_BOTH_BRD,
                                         xwinA=3, ywinA=3, xwinI=3, ywinI=3, NP=None,
                                         jobid=jobid, queue_mygauge=queue_mygauge,
                                         patch_outpaths=patch_outpaths)

    matches = {}  # maps {int ballotid: ((x1,y1,x2,y2), float score, str patchpath)}
    for imgpath, (x1,y1,response) in tm_matches.iteritems():
        ballotid = img2bal[imgpath]
        outpath = patch_outpaths[imgpath]
        matches[ballotid] = ((x1,y1,x1+w_attr,y1+h_attr),response,outpath)

    return matches, patchpath2bal, attrbox

def compute_mult_exemplars(proj, boxes_map, bal2imgs, img2page, patch2bal, bal2patches, attrprops,
                           queue_mygauge=None):
    """
    Input:
        obj PROJ:
        dict BOXES_MAP: {int ballotid: [AttrBox_i, ...]}
        dict BAL2IMGS:
        dict IMG2PAGE:
        dict PATCH2BAL: {str patchpath: (int ballotid, attrtype, attrval)}
        dict BAL2PATCHES: {int ballotid: [(patchpath, attrtype, attrval), ...]}
        dict ATTRPROPS: {str ATTRMODE: {str attrtype: dict PROPS}}
            where ATTRMODE in ('DIGITBASED', 'IMGBASED', 'CUSTATTR')
            and PROPS has keys: 'attrtype', 'x1','y1','x2','y2', 'is_tabulationonly',
                                'side', 'grp_per_partition', 'num_digits'
    Output:
        dict MULTEXEMPLARS_MAP: {str attrtype: {str attrval: [(subpatchP, blankpath, (x1,y1,x2,y2)), ...]}}
            subpatchP := This should point to the exemplar patch itself
            blankpathP := Points to the (entire) voted image that subpatchP came from
            (x1,y1,x2,y2) := BB that, from blankpathP, created subpatchP
    """
    def is_part_consistent(attrtype):
        return attrprops['IMGBASED'][attrtype]['grp_per_partition']

    if not common.exists_imgattrs(proj):
        return None
    
    type2valpatches = {} # maps {attrtype: {attrval: ((imgpath_i, (y1,y2,x1,x2)), ...)}}
    for patchpath, (ballotid, attrtype, attrval) in patch2bal.iteritems():
        # We have already extracted each patch path during find_attr_matches,
        # so just use them directly. bb=None => Use entire img.
        type2valpatches.setdefault(attrtype, {}).setdefault(attrval, []).append((patchpath, None))
    attrtype_exemplars = {} # maps {str attrtype: {attrval: [(imgpath_i, (y1,y2,x1,x2)), ...]}}
    for attrtype, attrvalpatches in type2valpatches.iteritems():
        if is_part_consistent(attrtype):
            print "(Info) Attribute '{0}' is consistent within partitions, \
no need to compute multiple exemplars for this.".format(attrtype)
            continue
        print "...attr '{0}': Finding multiple exemplars...".format(attrtype)
        exemplars = group_attrs.compute_exemplars_fullimg(attrvalpatches)
        print "...attr '{0}': {1} exemplars were found.".format(attrtype, sum(map(len, exemplars.values())))
        attrtype_exemplars[attrtype] = exemplars
        if queue_mygauge != None:
            queue_mygauge.put(True)
    
    def get_attr_box(attrtype, ballotid):
        for box in boxes_map[ballotid]:
            if '_'.join(sorted(box.attrtypes)) == attrtype:
                return box
        return None

    # 2.) Save each exemplar to proj.attrexemplars_dir
    outdir = pathjoin(proj.projdir_path, proj.attrexemplars_dir)
    multexemplars_map = {} # maps {attrtype: {attrval: [(subpatchpath_i, blankpath_i, bb_i), ...]}}
    for attrtype, _dict in attrtype_exemplars.iteritems():
        rootdir = pathjoin(outdir, attrtype)
        try: os.makedirs(rootdir)
        except: pass
        for attrval, info in _dict.iteritems():
            for i, (patchpath, bb) in enumerate(info):
                # note: BB is (y1,y2,x1,x2)
                I = cv.LoadImage(patchpath, cv.CV_LOAD_IMAGE_GRAYSCALE)
                if bb == None:
                    # If BB is None, use the entire image
                    w, h = cv.GetSize(I)
                    bb = (0, h-1, 0, w-1)

                cv.SetImageROI(I, (bb[2], bb[0], bb[3]-bb[2], bb[1]-bb[0]))
                outname = "{0}_{1}.png".format(attrval, i)
                fulloutpath = pathjoin(rootdir, outname)
                cv.SaveImage(fulloutpath, I)
                (ballotid, atype, aval) = patch2bal[patchpath]
                assert attrtype == atype, "ERROR: patch {0} had attrtype={1}, should be {2}".format(patchpath, atype, attrtype)
                attrbox = get_attr_box(atype, ballotid)
                assert attrbox != None, "ERROR: Couldn't find attrbox for atype={0}, ballotid={1}".format(atype, ballotid)
                imgpaths = sorted(bal2imgs[ballotid], key=lambda imP: img2page[imP])
                imgpath = imgpaths[attrbox.side]
                bbout = attrbox.x1, attrbox.y1, attrbox.x2, attrbox.y2
                multexemplars_map.setdefault(attrtype, {}).setdefault(attrval, []).append((fulloutpath, imgpath, bbout))
    return multexemplars_map

class ThreadFindAttrMatches(threading.Thread):
    def __init__(self, ballots_todo, src_balid, attrbox, attrpatch_outdir, voteddir,
                 bal2imgs, img2bal,
                 img2flip, img2page,
                 exemplar_imgpath,
                 manager, queue_mygauge, 
                 jobid, thread_listener, callback, *args, **kwargs):
        threading.Thread.__init__(self, *args, **kwargs)
        self.ballots_todo = ballots_todo
        self.src_balid = src_balid
        self.attrbox = attrbox
        self.attrpatch_outdir = attrpatch_outdir
        self.voteddir = voteddir
        self.bal2imgs = bal2imgs
        self.img2bal = img2bal
        self.img2flip = img2flip
        self.img2page = img2page
        self.exemplar_imgpath = exemplar_imgpath
        self.manager = manager
        self.queue_mygauge = queue_mygauge
        self.jobid = jobid
        self.thread_listener = thread_listener
        self.callback = callback
    def run(self):
        matches, patchpath2bal, attrbox = find_attr_matches(self.ballots_todo, self.src_balid,
                                                            self.attrbox,
                                                            self.attrpatch_outdir, self.voteddir,
                                                            self.bal2imgs, self.img2bal, 
                                                            self.img2flip, self.img2page,
                                                            self.exemplar_imgpath,
                                                            self.queue_mygauge, self.jobid)
        self.thread_listener.stop_listening()
        wx.CallAfter(Publisher().sendMessage, "signals.MyGauge.done", (self.jobid,))
        wx.CallAfter(self.callback, matches, patchpath2bal, attrbox)

class ThreadComputeMultExemplars(threading.Thread):
    def __init__(self, proj, boxes_map, bal2imgs, img2page, patch2bal,
                 bal2patches, attrprops, queue_mygauge, jobid, callback, tlisten, *args, **kwargs):
        threading.Thread.__init__(self, *args, **kwargs)
        self.proj, self.boxes_map, self.bal2imgs, self.img2page = proj, boxes_map, bal2imgs, img2page
        self.patch2bal, self.bal2patches, self.attrprops = patch2bal, bal2patches, attrprops
        self.queue_mygauge, self.jobid = queue_mygauge, jobid
        self.callback, self.tlisten = callback, tlisten
    def run(self):
        multexemplars_map = compute_mult_exemplars(self.proj, self.boxes_map, self.bal2imgs, self.img2page,
                                                   self.patch2bal, self.bal2patches, self.attrprops,
                                                   queue_mygauge=self.queue_mygauge)
        self.tlisten.stop_listening()
        wx.CallAfter(Publisher().sendMessage, "signals.MyGauge.done", (self.jobid,))
        wx.CallAfter(self.callback, multexemplars_map)

class ThreadListener(threading.Thread):
    def __init__(self, queue_mygauge, jobid, *args, **kwargs):
        threading.Thread.__init__(self, *args, **kwargs)
        self.queue_mygauge = queue_mygauge
        self.jobid = jobid
        self._stop = threading.Event()

    def i_am_listening(self):
        return not self._stop.is_set()
    def stop_listening(self):
        self._stop.set()
    def run(self):
        while self.i_am_listening():
            try:
                val = self.queue_mygauge.get(block=True, timeout=1)
                wx.CallAfter(Publisher().sendMessage, "signals.MyGauge.tick", (self.jobid,))
            except Empty:
                pass

def main():
    pass

if __name__ == '__main__':
    main()
