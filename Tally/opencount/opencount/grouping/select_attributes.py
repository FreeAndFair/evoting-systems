import os, sys, time, pdb, threading, random
import cv, Image
import wx

try:
    import cPickle as pickle
except ImportError:
    import pickle

from os.path import join as pathjoin

sys.path.append('..')

import tempmatch, util, common
import specify_voting_targets.util_widgets as util_widgets
import specify_voting_targets.util_gui as util_gui
import verify_overlays_new
import grouping.group_attrs as group_attrs
import grouping.partask as partask

# Global CTR used to ensure unique filenames for outpatches.
CTR = 0

class SelectAttributesMasterPanel(wx.Panel):
    """ Panel meant to be directly integrated with OpenCount. """
    def __init__(self, parent, *args, **kwargs):
        wx.Panel.__init__(self, parent, *args, **kwargs)
        
        self.project = None
        # BOXES := {str ballotid: [((x1, y1, x2, y2), str attrtype, str attrval, str patchpath, subpatchP), ...]}
        self.boxes = None

        # self.MAPPING := {str imgpath: {str attrtype: str patchpath}}
        self.mapping = None
        # self.INV_MAPPING := {str patchpath: (imgpath, attrtype)}
        self.inv_mapping = None

        # maps {str attrtype: [(attrval, i, str patchpath, str blankpath (x1,y1,x2,y2)), ...]}
        self.usersel_exs = {} 

        self.attridx = None
        self.attrtypes = None

        # NUM_EXMPLS: Number of ballots to randomly select
        self.NUM_EXMPLS = 1000

        # self.STATEFILEP := Location of statefile.
        self.statefileP = None

        self.selectattrs = SelectAttributesPanel(self)

        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.sizer.Add(self.selectattrs, proportion=1, flag=wx.EXPAND)
        self.SetSizer(self.sizer)

    def start(self, proj):
        def exists_imgattr(attrs):
            for attr in attrs:
                if not attr['is_digitbased']:
                    return True
            return False
        # First check to see if there even exist any img-based attributes
        attrs = pickle.load(open(proj.ballot_attributesfile, 'rb'))
        if not exists_imgattr(attrs):
            print "...No Img-based attributes in this election..."
            return
        self.project = proj
        self.img2flip = pickle.load(open(pathjoin(proj.projdir_path,
                                                  proj.image_to_flip), 'rb'))
        if self.stop not in proj.closehook:
            proj.addCloseEvent(self.stop)
        self.statefileP = pathjoin(proj.projdir_path, '_selectattrs_state.p')
        if self.load_session():
            print "...Loaded Select Attributes State..."
            self.attridx = 0
        else:
            self.boxes = {}
            self.usersel_exs = {}
            b2imgs = pickle.load(open(proj.ballot_to_images, 'rb'))
            img2page = pickle.load(open(pathjoin(proj.projdir_path, proj.image_to_page), 'rb'))
            partition_exmpls = pickle.load(open(pathjoin(proj.projdir_path,
                                                         proj.partition_exmpls), 'rb'))
            # Randomly choose self.NUM_EXMPLS ballots from the election
            bal2partition = pickle.load(open(pathjoin(proj.projdir_path,
                                                      proj.partitions_invmap), 'rb'))
            candidate_balids = bal2partition.keys()
            num_ballots = len(candidate_balids)
            
            chosen_ballotids = set()
            if num_ballots <= self.NUM_EXMPLS:
                chosen_ballotids = set(candidate_balids)
            else:
                _cnt = 0
                UPPER = min(self.NUM_EXMPLS, num_ballots)
                while _cnt < UPPER:
                    idx = random.randrange(num_ballots)
                    balid = candidate_balids[idx]
                    if balid not in chosen_ballotids:
                        chosen_ballotids.add(balid)
                        _cnt += 1
            blanks = [] # list of [[path_page0, path_page1, ...], ...]
            for ballotid in chosen_ballotids:
                imgpaths = b2imgs[ballotid]
                imgpaths_ordered = sorted(imgpaths, key=lambda imP: img2page[imP])
                blanks.append(imgpaths_ordered)
            self.mapping, self.inv_mapping = do_extract_attr_patches(proj, blanks, self.img2flip)
            self.attrtypes = list(common.get_attrtypes(proj, with_digits=False))
            self.attridx = 0
        self.do_labelattribute(self.attridx)
        self.Fit()
    def stop(self):
        if not self.project:
            return
        self.project.removeCloseEvent(self.stop)
        self.save_boxes()
        self.save_session()
        self.export_results()

    def load_session(self):
        """ Attempts to restore a previously-stored state. Returns True if
        successful, False otherwise.
        """
        if self.statefileP == None:
            return False
        try:
            state = pickle.load(open(self.statefileP, 'rb'))
            self.boxes = state['boxes']
            self.mapping = state['mapping']
            self.inv_mapping = state['inv_mapping']
            self.attrtypes = state['attrtypes']
            self.usersel_exs = state['usersel_exs']
        except:
            return False
        return True

    def save_session(self):
        """ Saves the current session to a statefile. """
        if not self.statefileP:
            return False
        f = open(self.statefileP, 'wb')
        state = {"boxes": self.boxes,
                 "mapping": self.mapping,
                 "inv_mapping": self.inv_mapping,
                 "attrtypes": self.attrtypes,
                 "usersel_exs": self.usersel_exs}
        pickle.dump(state, f, pickle.HIGHEST_PROTOCOL)
        print "...saved Select Attributes state..."
        return True

    def export_results(self):
        """ Computes multiple exemplars. Also
        saves the attribute labelling results to proj.partition_attrmap.
        """
        if not self.boxes:
            return
        self.save_boxes()
        print "...Exporting Select Attributes Results..."
        img2b = pickle.load(open(self.project.image_to_ballot, 'rb'))
        partition_attrmap = {} # maps {int partitionID: [[imgpath, x, y, width, height, attrtype,
                               #                          attrval, page, is_digitbased, is_tabulationonly], ...]
        partitions_map = pickle.load(open(pathjoin(self.project.projdir_path,
                                                   self.project.partitions_map), 'rb'))
        partitions_invmap = pickle.load(open(pathjoin(self.project.projdir_path,
                                                      self.project.partitions_invmap), 'rb'))
        header = ("imgpath", "id", "x", "y", "width", "height", "attr_type",
                  "attr_val", "side", "is_digitbased", "is_tabulationonly")
        uid = 0
        for imgpath, info in self.boxes.iteritems():
            ballotid = img2b[imgpath]
            partitionID = partitions_invmap[ballotid]
            attrs_list = [] # [[imP,x,y,w,h,attrtype,attrval,page,isdigitbased,istabonly],...]
            for ((x1, y1, x2, y2), attrtype, attrval, patchpath, subpatchP) in info:
                attrside = common.get_attr_prop(self.project, attrtype, 'side')
                isdigitbased = common.get_attr_prop(self.project, attrtype, "is_digitbased")
                istabonly = common.get_attr_prop(self.project, attrtype, "is_tabulationonly")
                row = {"imgpath": imgpath, "id": uid,
                       "x": x1, "y": y1,
                       "width": int(round(x2 - x1)),
                       "height": int(round(y2 - y1)),
                       "attr_type": attrtype, "attr_val": attrval,
                       "side": attrside,
                       "is_digitbased": isdigitbased,
                       "is_tabulationonly": istabonly}
                attrs_list.append([imgpath, x1, y1, x2-x1,y2-y1, attrtype, attrval,
                                   attrside, isdigitbased, istabonly])
                uid += 1
            partition_attrmap.setdefault(partitionID, []).extend(attrs_list)
        pickle.dump(partition_attrmap, open(pathjoin(self.project.projdir_path,
                                                     self.project.partition_attrmap), 'wb'),
                    pickle.HIGHEST_PROTOCOL)
        outdir = os.path.join(self.project.projdir_path,
                              self.project.attrexemplars_dir)
        self.cluster_attr_patches(outdir)

    def cluster_attr_patches(self, outdir):
        """ Try to discover multiple exemplars within the blank ballot
        img-based attribute patches (say, multi-backgrounds). MULTEXEMPLARS_MAP
        is a dict mapping:
            {str attrtype: {str attrval: ([subpatchP, blankpathP, (x1,y1,x2,y2)], ...)}}
        """
        if not common.exists_imgattrs(self.project):
            return
        # 0.) Create+populate the BLANKPATCHES dict
        blankpatches = {} # maps {attrtype: {attrval: [(subpatchpath_i, bb_i), ...]}}
        subpatch_map = {} # maps {str subpatchP: (str patchP, (x1,y1,x2,y2))}
        for ballotid, info in self.boxes.iteritems():
            for (bb, attrtype, attrval, patchpath, subpatchP) in info:
                blankpatches.setdefault(attrtype, {}).setdefault(attrval, []).append((subpatchP, None))
                subpatch_map[subpatchP] = (patchpath, bb)
        # 1.) For each attrval of each attrtype, run the clustering
        attrtype_exemplars = {} # maps {attrtype: {attrval: [(patchpath_i, bb_i), ...]}}
        for attrtype, attrvalmap in blankpatches.iteritems():
            print "...running on attrtype: {0}...".format(attrtype)
            exemplars = group_attrs.compute_exemplars_fullimg(attrvalmap)
            _n = sum(map(len, exemplars.values()))
            print "...For Attribute {0}, {1} exemplars were found.".format(attrtype, _n)
            attrtype_exemplars[attrtype] = exemplars
        # 2.) Export results.
        outfile_map = {} # maps {attrtype: {attrval: [(subpatchpath_i, blankpath_i, bb_i), ...]}}
        for attrtype, _dict in attrtype_exemplars.iteritems():
            rootdir = pathjoin(outdir, attrtype)
            try:
                os.makedirs(rootdir)
            except:
                pass
            for attrval, info in _dict.iteritems():
                for i, (subpatchP, bb_none) in enumerate(info):
                    patchpath, bb = subpatch_map[subpatchP]
                    blankpath, _ = self.inv_mapping[patchpath]
                    I = cv.LoadImage(subpatchP, cv.CV_LOAD_IMAGE_UNCHANGED)
                    if bb_none != None:
                        cv.SetImageROI(I, (bb_none[2], bb_none[0], bb_none[3]-bb_none[2], bb_none[1]-bb_none[0]))
                    outname = "{0}_{1}.png".format(attrval, i)
                    fulloutpath = pathjoin(rootdir, outname)
                    cv.SaveImage(fulloutpath, I)
                    x1,y1,x2,y2 = bb
                    bbout = (x1,y1,x2,y2)
                    outfile_map.setdefault(attrtype, {}).setdefault(attrval, []).append((subpatchP, blankpath, bbout))
        # 3.) Also add in the user-selected patches in 'Label Attributes'
        # as additional exemplars.
        for attrtype, tups in self.usersel_exs.iteritems():
            for (attrval, i, subpatchpath, blankpath, bb) in tups:
                outfile_map[attrtype][attrval].append((subpatchpath, blankpath, bb))
        pickle.dump(outfile_map, open(pathjoin(self.project.projdir_path,
                                               self.project.multexemplars_map), 'wb'))
        print "...Done saving multexemplar patches..."
    
    def do_labelattribute(self, attridx):
        """ Sets up UI to allow user to label attribute at ATTRIDX.
        """
        self.attridx = attridx
        curattrtype = self.attrtypes[attridx]
        
        boxes = {}
        patchpaths = []
        # 1.) Populate the PATCHPATHS list
        for patchpath, (imgpath, attrtype) in self.inv_mapping.iteritems():
            if attrtype == curattrtype:
                patchpaths.append(patchpath)
        # 2.) Populate the BOXES dict with previously-created boxes, if any
        for ballotid, info in self.boxes.iteritems():
            for ((x1,y1,x2,y2), attrtype, attrval, patchpath, subpatchP) in info:
                if attrtype != curattrtype: 
                    continue
                # Note: These coords are wrt entire image, whereas self.SELECTATTRS
                # expects coords to be wrt patch. Do a correction.
                x = common.get_attr_prop(self.project, attrtype, 'x1')
                y = common.get_attr_prop(self.project, attrtype, 'y1')
                x1_off, y1_off = x1 - x, y1 - y
                x2_off, y2_off = x2 - x, y2 - y
                boxes.setdefault(patchpath, []).append(((x1_off,y1_off,x2_off,y2_off), attrval, subpatchP))
        outdir0 = os.path.join(self.project.projdir_path, 'selectattr_outdir0')
        self.selectattrs.start(patchpaths, self.img2flip, curattrtype, boxes=boxes, outdir0=outdir0)
        self.selectattrs.mosaicpanel.txt_attrtype.SetLabel("{0} ({1} / {2}).".format(curattrtype, attridx+1, len(self.attrtypes)))
        self.Layout()
        return self.attridx

    def save_boxes(self):
        """ Saves current boxes from self.SELECTATTRS into my self.BOXES
        property.
        """
        if not self.selectattrs.boxes:
            return
        for patchpath, boxes in self.selectattrs.boxes.iteritems():
            imgpath, attrtype = self.inv_mapping[patchpath]
            x = common.get_attr_prop(self.project, attrtype, 'x1')
            y = common.get_attr_prop(self.project, attrtype, 'y1')
            # Replace all entries in self.BOXES for ATTRTYPE with 
            # entries in self.SELECTATTRS.BOXES
            self.boxes.setdefault(imgpath, [])
            self.boxes[imgpath] = [tup for tup in self.boxes[imgpath] if tup[1] != attrtype]
            for ((x1, y1, x2, y2), label, subpatchP) in boxes:
                # Note: coords are wrt PATCH, not entire ballot image. Do
                # a correction.
                x1_off, y1_off = x1 + x, y1 + y
                x2_off, y2_off = x2 + x, y2 + y
                self.boxes[imgpath].append(((x1_off, y1_off, x2_off, y2_off), attrtype, label, patchpath, subpatchP))

    def next_attribute(self):
        newidx = self.attridx + 1
        if newidx < 0 or newidx >= len(self.attrtypes):
            return False
        self.save_boxes()
        return self.do_labelattribute(newidx)
    def prev_attribute(self):
        newidx = self.attridx - 1
        if newidx < 0 or newidx >= len(self.attrtypes):
            return False
        self.save_boxes()
        return self.do_labelattribute(newidx)
    def validate_outputs(self):
        return True
    def checkCanMoveOn(self):
        return True

class SelectAttributesPanel(wx.Panel):
    def __init__(self, parent, *args, **kwargs):
        wx.Panel.__init__(self, parent, *args, **kwargs)
        self.parent = parent

        self.patchpaths = None
        self.attr = None
        # maps {str patchpath: [((x1, y1, x2, y2), str label, str subpatchP) ...]}
        # Note: These x1,y1 coords are wrt the PATCH image, not the entire
        #       ballot image.
        self.boxes = {}

        # OUTDIR0: Stores the selected regions that the user made, on 
        # each attribute patch. 
        self.outdir0 = 'select_attr_outdir0'

        #self.mosaicpanel = util_widgets.MosaicPanel(self, imgmosaicpanel=AttrMosaicPanel,
        #                                            CellClass=PatchPanel, CellBitmapClass=PatchBitmap)
        self.mosaicpanel = MosaicPanel_sub(self)

        sizer = wx.BoxSizer(wx.VERTICAL)
        sizer.Add(self.mosaicpanel, proportion=1, flag=wx.EXPAND)
        self.SetSizer(sizer)
        self.Fit()
        
    def start(self, patchpaths, img2flip, attr, boxes=None, outdir0=None):
        self.patchpaths = patchpaths
        self.img2flip = img2flip
        self.attr = attr
        self.boxes = boxes if boxes != None else {}
        if outdir0 != None:
            self.outdir0 = outdir0
        self.mosaicpanel.set_images(patchpaths)
        self.Fit()

class MosaicPanel_sub(util_widgets.MosaicPanel):
    def __init__(self, parent, *args, **kwargs):
        util_widgets.MosaicPanel.__init__(self, parent, imgmosaicpanel=AttrMosaicPanel,
                                          CellClass=PatchPanel, CellBitmapClass=PatchBitmap,
                                          *args, **kwargs)
    def init_ui(self):
        util_widgets.MosaicPanel.init_ui(self)
        self.btn_sizer.Add((50, 0))
        self.btn_nextattr = wx.Button(self, label="Next Attribute")
        self.btn_prevattr = wx.Button(self, label="Previous Attribute")
        txt0 = wx.StaticText(self, label="Current Attribute: ")
        self.txt_attrtype = wx.StaticText(self, label="Foo (0/0).")
        btn_opts = wx.Button(self, label="Options...")
        btn_hide = wx.Button(self, label="Hide Labeled Patches")
        btn_show = wx.Button(self, label="Show Labeled Patches")
        self.btn_sizer.AddMany([(self.btn_nextattr,), (self.btn_prevattr,),
                                ((30,0),),
                                (txt0,), (self.txt_attrtype,),
                                ((50,0),),
                                (btn_opts,),
                                (btn_hide,), (btn_show,)])
        self.btn_nextattr.Bind(wx.EVT_BUTTON, lambda evt: self.GetParent().GetParent().next_attribute())
        self.btn_prevattr.Bind(wx.EVT_BUTTON, lambda evt: self.GetParent().GetParent().prev_attribute())
        btn_hide.Bind(wx.EVT_BUTTON, self.onButton_hide)
        btn_show.Bind(wx.EVT_BUTTON, self.onButton_show)
        btn_opts.Bind(wx.EVT_BUTTON, self.onButton_opts)
        self.Layout()

    def onButton_hide(self, evt):
        """ Only display patches that don't have a bounding box. """
        patchpaths = []
        for patchpath in self.GetParent().patchpaths:
            if not self.GetParent().boxes.get(patchpath, None):
                patchpaths.append(patchpath)
        self.set_images(patchpaths)

    def onButton_show(self, evt):
        """ Show all patches. """
        self.set_images(self.GetParent().patchpaths)

    def onButton_opts(self, evt):
        class OptsDialog(wx.Dialog):
            def __init__(self, parent, cur_thresh, *args, **kwargs):
                wx.Dialog.__init__(self, parent, title="Select Attributes Options", *args, **kwargs)

                self.thresh_out = cur_thresh

                txt0 = wx.StaticText(self, label="Template Matching Sensitivity: ")
                self.txtin_tmthresh = wx.TextCtrl(self, value=str(self.thresh_out))
                sizer0 = wx.BoxSizer(wx.HORIZONTAL)
                sizer0.AddMany([(txt0,), (self.txtin_tmthresh,)])

                btn_ok = wx.Button(self, label="Ok")
                btn_cancel = wx.Button(self, label="Cancel")
                btn_ok.Bind(wx.EVT_BUTTON, self.onButton_ok)
                btn_cancel.Bind(wx.EVT_BUTTON, self.onButton_cancel)
                btn_sizer = wx.BoxSizer(wx.HORIZONTAL)
                btn_sizer.AddMany([(btn_ok,), (btn_cancel,)])
                
                sizer = wx.BoxSizer(wx.VERTICAL)
                sizer.Add(sizer0)
                sizer.Add(btn_sizer, flag=wx.ALIGN_CENTER)

                self.SetSizer(sizer)
                self.Layout()
            def onButton_ok(self, evt):
                try:
                    self.thresh_out = float(self.txtin_tmthresh.GetValue())
                except:
                    print "Invalid input:", self.txtin_tmthresh.GetValue()
                self.EndModal(wx.ID_OK)
            def onButton_cancel(self, evt):
                self.EndModal(wx.ID_CANCEL)
                
        dlg = OptsDialog(self, self.imagemosaic.TM_THRESHOLD)
        status = dlg.ShowModal()
        if status == wx.ID_CANCEL:
            return
        self.imagemosaic.TM_THRESHOLD = dlg.thresh_out

class AttrMosaicPanel(util_widgets.ImageMosaicPanel):
    TEMPMATCH_JOB_ID = util.GaugeID("SelectAttrsTempMatchJobId")

    def __init__(self, parent, *args, **kwargs):
        util_widgets.ImageMosaicPanel.__init__(self, parent, cellheight=100, *args, **kwargs)

        # Threshold value to use for template matching
        self.TM_THRESHOLD = 0.85
        
        self._verifyframe = None
        
    def get_boxes(self, imgpath):
        '''
        boxes = self.GetParent().GetParent().boxes.get(imgpath, [])
        return boxes
        '''
        return []

    def start_tempmatch(self, patch, bb, patchpath):
        """ Run template matching on all unlabeled self.IMGPATHS, 
        searching for PATCH.
        Input:
            IplImage PATCH:
            tuple BB: (x1,y1,x2,y2), wrt the patch.
            str PATCHPATH: Path of the patch where PATCH comes from.
        """
        # 1.) Ask user what attr value this is
        dlg = AttrValueDialog(self, patch)
        status = dlg.ShowModal()
        if status == wx.ID_CANCEL:
            return
        attrval = dlg.attrval
        
        # Save PATCH to temp file for VerifyPanel to use later.
        attrtype = self.GetParent().GetParent().attr
        outrootdir = pathjoin(self.GetParent().GetParent().outdir0, 
                              'user_selected',
                              attrtype)
        try:
            os.makedirs(outrootdir)
        except:
            pass
        i = len(os.listdir(outrootdir))
        outfilepath = pathjoin(outrootdir, "{0}_{1}.png".format(attrval, i))
        cv.SaveImage(outfilepath, patch)
        cv.SaveImage("_selectattr_patch.png", patch)
        x = common.get_attr_prop(self.GetParent().GetParent().GetParent().project, attrtype, 'x1')
        y = common.get_attr_prop(self.GetParent().GetParent().GetParent().project, attrtype, 'y1')
        bb_off = bb[0]+x, bb[1]+y, bb[2]+x, bb[3]+y
        blankpath, _ = self.GetParent().GetParent().GetParent().inv_mapping[patchpath]
        self.GetParent().GetParent().GetParent().usersel_exs.setdefault(attrtype, []).append((attrval, i, outfilepath, blankpath, bb_off))
        
        # 2.) Only run template matching on un-labeled imgpaths
        unlabeled_imgpaths = []
        for imgpath in self.imgpaths:
            if imgpath not in self.GetParent().GetParent().boxes:
                unlabeled_imgpaths.append(imgpath)
                
        t = TM_Thread(patch, unlabeled_imgpaths, attrval, self.TEMPMATCH_JOB_ID,
                      callback=self.on_tempmatchdone)
        print "...starting TM Thread..."
        numtasks = len(unlabeled_imgpaths)
        gauge = util.MyGauge(self, numtasks, thread=t, msg="Running template matching...",
                             job_id=self.TEMPMATCH_JOB_ID)
        t.start()
        gauge.Show()

    def on_tempmatchdone(self, results, w, h, attrval):
        """
        Input:
            dict RESULTS: {str regionpath: (x, y, float score)}
            int W, H: Width/Height of patch being searched for.
        """
        print "...TempMatching done!"
        # 1.) Extract+Save imgs, so that ViewOverlays can access them.
        outpaths = []
        patch2img = {} # maps {str patchpath: str imgpath}
        #scores = []
        #for _, (_, _, score) in results.iteritems():
        #    scores.append(score)
        #hist, edges = np.histogram(scores)
        global CTR
        for regionpath, (x, y, score) in results.iteritems():
            if score < self.TM_THRESHOLD:
                continue
            I = cv.LoadImage(regionpath, cv.CV_LOAD_IMAGE_UNCHANGED)
            cv.SetImageROI(I,(x, y, w, h))
            imgname = os.path.split(regionpath)[1]
            imgname_noext = os.path.splitext(imgname)[0]
            outname = "{0}_{1}_{2}.png".format(imgname_noext, self.GetParent().GetParent().attr, CTR)
            # Use a global incrementing CTR to avoid problems if two different
            # ballots have the same imagename. 
            CTR += 1
            outrootdir = os.path.join(self.GetParent().GetParent().outdir0, self.GetParent().GetParent().attr)
            try:
                os.makedirs(outrootdir)
            except:
                pass
            outpath = os.path.join(outrootdir, outname)
            cv.SaveImage(outpath, I)
            outpaths.append(outpath)
            patch2img[outpath] = regionpath
        initgroups = [outpaths]
        exemplar_imP = '_selectattr_patch.png'
        self._verifyframe = verify_overlays_new.CheckImageEqualsFrame(None, outpaths,
                                                                      exemplar_imP,
                                                                      ondone=lambda verify_results: self.on_verifydone(verify_results, attrval, results, w, h, patch2img))
        self._verifyframe.Show()
        self._verifyframe.Maximize()

    def on_verifydone(self, verify_results, attrval, results, w, h, patch2img):
        """ 
        Input:
            list VERIFY_RESULTS: maps {tag: [imgpath_i, ...]}
            str ATTRVAL:
            dict RESULTS: maps {str imgpath: (x, y, float score)}
            int W, H: Size of patch
            dict PATCH2IMG: maps {str patchpath: str imgpath}
        """
        self._verifyframe.Close()
        self._verifyframe = None
        # Add all TAG_YES groups
        subpatchpaths = verify_results[verify_overlays_new.CheckImageEquals.TAG_YES]
        for subpatchpath in subpatchpaths:
            imgpath = patch2img[subpatchpath]
            (x, y, score) = results[imgpath]
            self.GetParent().GetParent().boxes.setdefault(imgpath, []).append(((x, y, x+w, y+h), attrval, subpatchpath))

        self.Refresh()

class TM_Thread(threading.Thread):
    def __init__(self, patch, regionpaths, attrval, jobid, callback=None, *args, **kwargs):
        threading.Thread.__init__(self, *args, **kwargs)
        self.patch = patch
        self.regionpaths = regionpaths
        self.callback = callback
        self.attrval = attrval
        self.jobid = jobid
    def run(self):
        print "...calling template matching..."
        t = time.time()
        results = tempmatch.bestmatch_par(self.patch, self.regionpaths, do_smooth=tempmatch.SMOOTH_BOTH,
                                          xwinA=3, ywinA=3, xwinI=3, ywinI=3, NP=12, jobid=self.jobid)
        dur = time.time() - t
        print "...finished template matching ({0} s)".format(dur)
        if self.callback:
            w, h = cv.GetSize(self.patch)
            wx.CallAfter(self.callback, results, w, h, self.attrval)

class AttrValueDialog(wx.Dialog):
    def __init__(self, parent, patch, *args, **kwargs):
        """
        Input:
            IplImage PATCH:
        """
        wx.Dialog.__init__(self, parent, title="What Attribute Value is this?", *args, **kwargs)
        self.patch = patch

        self.attrval = None
        
        patchpil = Image.fromstring("L", cv.GetSize(patch), patch.tostring())
        patchpil = patchpil.convert("RGB")
        wxbmp = util.pil2wxb(patchpil)
        
        self.sbitmap = wx.StaticBitmap(self, bitmap=wxbmp)

        txt0 = wx.StaticText(self, label="What is the Attribute Value? ")
        self.attrval_in = wx.TextCtrl(self, style=wx.TE_PROCESS_ENTER)
        self.attrval_in.Bind(wx.EVT_TEXT_ENTER, self.onPressEnter)
        sizer_in = wx.BoxSizer(wx.HORIZONTAL)
        sizer_in.Add(txt0)
        sizer_in.Add(self.attrval_in)

        btn_ok = wx.Button(self, label="Ok")
        btn_cancel = wx.Button(self, label="Cancel")
        btn_ok.Bind(wx.EVT_BUTTON, self.onButton_ok)
        btn_cancel.Bind(wx.EVT_BUTTON, lambda evt: self.EndModal(wx.ID_CANCEL))
        btn_sizer = wx.BoxSizer(wx.HORIZONTAL)
        btn_sizer.AddMany([(btn_ok,), (btn_cancel,)])

        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.sizer.Add(self.sbitmap, flag=wx.ALIGN_CENTER)
        self.sizer.Add(sizer_in)
        self.sizer.Add(btn_sizer, flag=wx.ALIGN_CENTER)

        self.SetSizer(self.sizer)
        self.Fit()
        self.attrval_in.SetFocus()
    def onPressEnter(self, evt):
        self.onButton_ok(None)
    def onButton_ok(self, evt):
        self.attrval = self.attrval_in.GetValue()
        self.EndModal(wx.ID_OK)

class PatchPanel(util_widgets.CellPanel):
    def __init__(self, *args, **kwargs):
        util_widgets.CellPanel.__init__(self, *args, **kwargs)
        
    def onLeftDown(self, evt):
        pass

class PatchBitmap(util_widgets.CellBitmap):
    def __init__(self, *args, **kwargs):
        util_widgets.CellBitmap.__init__(self, *args, **kwargs)
        self.Bind(wx.EVT_LEFT_DOWN, self.onLeftDown)
        self.Bind(wx.EVT_LEFT_UP, self.onLeftUp)
        self.Bind(wx.EVT_MOTION, self.onMotion)

        self.newbox = None

    def onLeftDown(self, evt):
        if self.GetParent().is_dummy:
            return
        x, y = evt.GetPositionTuple()
        w_bmp, h_bmp = self.bitmap.GetSize()
        if x >= w_bmp or y >= h_bmp:
            return
        if not self.GetParent().GetParent().GetParent().GetParent().boxes.get(self.GetParent().imgpath, []):
            # Can only have one box at a time
            self.newbox = [None, None, None, None]
            self.newbox[:2] = self.c2img(x,y)
            self.newbox[2] = self.newbox[0]+1
            self.newbox[3] = self.newbox[1]+1
        self.Refresh()

    def onLeftUp(self, evt):
        if self.GetParent().is_dummy:
            return
        x, y = evt.GetPositionTuple()
        w_bmp, h_bmp = self.bitmap.GetSize()
        x = min(x, w_bmp-1)
        y = min(y, h_bmp-1)
        if self.newbox:
            self.newbox[2:] = self.c2img(x,y)
            box = normbox(self.newbox)
            self.newbox = None
            I = cv.LoadImage(self.GetParent().imgpath, cv.CV_LOAD_IMAGE_GRAYSCALE)
            x1,y1,x2,y2 = box
            cv.SetImageROI(I, (x1, y1, x2-x1, y2-y1))
            self.GetParent().GetParent().start_tempmatch(I, (x1,y1,x2,y2), self.GetParent().imgpath)
        self.Refresh()

    def onMotion(self, evt):
        if self.GetParent().is_dummy:
            return
        x, y = evt.GetPositionTuple()
        w_bmp, h_bmp = self.bitmap.GetSize()
        x = min(x, w_bmp-1)
        y = min(y, h_bmp-1)
        if self.newbox:
            self.newbox[2:] = self.c2img(x,y)
            self.Refresh()

    def c2img(self, x, y):
        return map(lambda n: int(round(n)), (x * self.scale, y * self.scale))
    def img2c(self, x, y):
        return map(lambda n: int(round(n)), (x / self.scale, y / self.scale))

    def onPaint(self, evt):
        dc = util_widgets.CellBitmap.onPaint(self, evt)
        if self.GetParent().is_dummy:
            return
        boxes = self.GetParent().GetParent().GetParent().GetParent().boxes.get(self.GetParent().imgpath, [])
        if boxes:
            txtfont = wx.Font(14, wx.FONTFAMILY_DEFAULT, 
                              wx.FONTSTYLE_NORMAL, wx.FONTWEIGHT_BOLD)
            dc.SetTextForeground("Blue")
            dc.SetFont(txtfont)
            for (box, label, subpatchP) in boxes:
                x1, y1 = self.img2c(*box[:2])
                x2, y2 = self.img2c(*box[2:])
                w, h = x2 - x1, y2 - y1
                dc.SetPen(wx.Pen("Green", 4))
                dc.DrawRectangle(x1, y1, w, h)
                w_txt, h_txt = dc.GetTextExtent(label)
                x_txt, y_txt = x1, y1-h_txt
                if y_txt < 0:
                    y_txt = y1 + h
                dc.DrawText(label, x_txt, y_txt)
        if self.newbox:
            x1, y1, x2, y2 = normbox(self.newbox)
            x1, y1 = self.img2c(x1, y1)
            x2, y2 = self.img2c(x2, y2)
            dc.SetPen(wx.Pen("Red", 2))
            dc.DrawRectangle(x1, y1, x2-x1, y2-y1)

def do_extract_attr_patches(proj, blanks, img2flip):
    """Extract all attribute patches from all blank ballots into
    the specified outdir. Saves them to:
        <projdir>/extract_attrs_templates/ATTRTYPE/*.png
    Input:
        list BLANKS: List of [[imgP_side0, imgP_side1, ...], ...]
    Output:
        (dict mapping, dict inv_mapping, where:
          mapping is {imgpath: {str attrtype: str patchpath}}
          inv_mapping is {str patchpath: (imgpath, attrtype)}
    """
    mapping, invmapping, blank2attrpatch, invb2ap = partask.do_partask(extract_attr_patches,
                                                                       blanks,
                                                                       _args=(proj, img2flip),
                                                                       combfn=_extract_combfn,
                                                                       init=({}, {}, {}, {}),
                                                                       N=1)
    blank2attrpatchP = pathjoin(proj.projdir_path,
                                proj.blank2attrpatch)
    pickle.dump(blank2attrpatch, open(blank2attrpatchP, 'wb'))
    invblank2attrpatchP = pathjoin(proj.projdir_path,
                                   proj.invblank2attrpatch)
    pickle.dump(invb2ap, open(invblank2attrpatchP, 'wb'))
    return mapping, invmapping
    
def _extract_combfn(result, subresult):
    """ Aux. function used for the partask.do_partask interface.
    Input:
        result: (dict mapping_0, dict invmapping_0, dict blank2attrpatch_0, dict invb2ap_0)
        subresult: (dict mapping_1, dict invmapping_1, dict blank2attrpach_1, dict invb2ap_1)
    Output:
        The result of 'combining' result and subresult:
            (dict mapping*, dict invmapping*, dict blank2attrpatch*, dict invb2ap*)
    """
    mapping, invmapping, blank2attrpatch, invblank2attrpatch = result
    mapping_sub, invmapping_sub, blank2attrpatch_sub, invblank2attrpatch_sub = subresult
    new_mapping = dict(mapping.items() + mapping_sub.items())
    new_invmapping = dict(invmapping.items() + invmapping_sub.items())
    new_blank2attrpatch = dict(blank2attrpatch) # maps {str imgpath: {str attrtype: str patchpath}}
    for imgpath, subdict in blank2attrpatch_sub.iteritems():
        for attrtype, patchpath in subdict.iteritems():
            new_blank2attrpatch.setdefault(imgpath, {})[attrtype] = patchpath
    # invblank2attrpatch maps {patchpath: (imgpath, attrtype)}
    new_invblank2attrpatch = dict(invblank2attrpatch.items() + invblank2attrpatch_sub.items())
    return (new_mapping, new_invmapping, new_blank2attrpatch, new_invblank2attrpatch)

def extract_attr_patches(blanks, (proj, img2flip)):
    """
    Extracts all image-based attributes from blank ballots, and saves
    the patches to the outdir proj.labelattrs_patchesdir.
    Input:
        list blanks: Of the form ((frontpath_i, backpath_i), ...)
        obj proj:
    Output:
        (dict mapping, dict inv_mapping, dict blank2attrpatch)
    """
    outdir = os.path.join(proj.projdir_path,
                          proj.extract_attrs_templates)
    # list of marshall'd attrboxes (i.e. dicts)
    ballot_attributes = pickle.load(open(proj.ballot_attributesfile, 'rb'))
    mapping = {} # maps {imgpath: {str attrtypestr: str patchPath}}
    inv_mapping = {} # maps {str patchPath: (imgpath, attrtypestr)}
    blank2attrpatch = {} # maps {str imgpath: {str attrtype: str patchpath}}
    invblank2attrpatch = {} # maps {str patchpath: (imgpath, attrtype)}
    for blankpaths in blanks:
        for blankside, imgpath in enumerate(blankpaths):
            for attr in ballot_attributes:
                if attr['is_digitbased']:
                    continue
                imgname =  os.path.split(imgpath)[1]
                attrside = attr['side']
                x1 = attr['x1']
                y1 = attr['y1']
                x2 = attr['x2']
                y2 = attr['y2']
                attrtype = common.get_attrtype_str(attr['attrs'])
                if blankside == attrside:
                    # patchP: if outdir is: 'labelattrs_patchesdir',
                    # imgpath is: '/media/data1/election/blanks/foo/1.png',
                    # proj.templatesdir is: '/media/data1/election/blanks/
                    # Recreate directory structure.
                    tmp = proj.voteddir
                    if not tmp.endswith('/'):
                        tmp += '/'
                    partdir = os.path.split(imgpath[len(tmp):])[0] # foo/
                    patchrootDir = pathjoin(outdir,
                                            partdir,
                                            os.path.splitext(imgname)[0])
                    # patchrootDir: labelattrs_patchesdir/foo/1/
                    util_gui.create_dirs(patchrootDir)
                    patchoutP = pathjoin(patchrootDir, "{0}_{1}.png".format(os.path.splitext(imgname)[0],
                                                                            attrtype))
                    blank2attrpatch.setdefault(imgpath, {})[attrtype] = patchoutP
                    invblank2attrpatch[patchoutP] = (imgpath, attrtype)
                    if not os.path.exists(patchoutP):
                    #if True:
                        # TODO: Only extract+save the imge patches
                        # when you /have/ to.
                        # shared.standardImread: ~0.40s
                        # scipy.misc.imread: ~0.192s
                        # PIL: ~0.168s
                        # OpenCV: ~0.06s
                        if abs(y1-y2) == 0 or abs(x1-x2) == 0:
                            print "Uh oh, about to crash. Why is this happening?"
                            print "    (y1,y2,x1,x2):", (y1,y2,x1,x2)
                            pdb.set_trace()
                        img = cv.LoadImage(imgpath, cv.CV_LOAD_IMAGE_GRAYSCALE)
                        if img2flip[imgpath]:
                            cv.Flip(img, img, flipMode=-1)
                        cv.SetImageROI(img, (int(x1), int(y1), int(x2-x1), int(y2-y1)))
                        cv.SaveImage(patchoutP, img)
                        
                    mapping.setdefault(imgpath, {})[attrtype] = patchoutP
                    inv_mapping[patchoutP] = (imgpath, attrtype)
    return mapping, inv_mapping, blank2attrpatch, invblank2attrpatch

def normbox((x1,y1,x2,y2)):
    return (min(x1,x2), min(y1,y2), max(x1, x2), max(y1,y2))

def main():
    class TestFrame(wx.Frame):
        def __init__(self, parent, patchpaths, *args, **kwargs):
            wx.Frame.__init__(self, parent, title="Select Attributes Test Frame",
                              size=(800, 800), *args, **kwargs)
            self.patchpaths = patchpaths

            self.mainpanel = SelectAttributesPanel(self)
            self.mainpanel.start(patchpaths, "AttrName")

    args = sys.argv[1:]
    patchdir = args[0]
    patchpaths = []
    for dirpath, dirnames, filenames in os.walk(patchdir):
        for imgname in [f for f in filenames if f.endswith('.png')]:
            patchpaths.append(os.path.join(dirpath, imgname))
    app = wx.App(False)
    f = TestFrame(None, patchpaths)
    f.Show()
    app.MainLoop()

if __name__ == '__main__':
    main()
