import sys, os, pdb, Queue, threading, time, traceback, random, argparse, math
try:
    import cPickle as pickle
except ImportError as e:
    import pickle

import wx, cv, scipy, Image
import wx.lib.colourchooser
import wx.lib.scrolledpanel
from wx.lib.pubsub import Publisher

import numpy as np
from os.path import join as pathjoin

sys.path.append('..')
import util
from specify_voting_targets import util_gui
from pixel_reg import shared
from grouping import common, verify_overlays_new, partask
from panel_opencount import OpenCountPanel

"""
Assumes extracted_dir looks like:
    <projdir>/extracted_attrs/precinct/*.png
Where each *.png is the result of encodepath'ing a blank ballot
id.
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

# Used to give a unique ID to all Digit-template-match matches.
matchID = 0

def get_last_matchID(imgsdir):
    """ Given the directory of saved imgmatches, return the last
    matchID. imgsdir would be like:
        <projdir>/digit_exemplars/<i>_examples/*
    Assumes that match paths are of the form:
        <matchID>_match.png
    i.e.:
        0_match.png
        1_match.png
        ...
    """
    i = 0
    for dirpath, dirnames, filenames in os.walk(imgsdir):
        for imgname in [f for f in filenames if util_gui.is_image_ext(f)]:
            curidx = int(imgname.split("_")[0])
            if curidx > i:
                i = curidx
    return i

class LabelDigitsPanel(OpenCountPanel):
    """ A wrapper-class of DigitMainPanel that is meant to be
    integrated into OpenCount itself.
    """
    def __init__(self, parent, *args, **kwargs):
        OpenCountPanel.__init__(self, parent, *args, **kwargs)
        self.parent = parent
        self.project = None

    def start(self, project):
        """ First, extract all digit-patches into 
        self.project.extracted_digitpatch_dir. Then, run the 
        Digit-Labeling UI.
        """
        self.project = project
        extracted_digitpatches_fulldir = pathjoin(project.projdir_path,
                                                  project.extracted_digitpatch_dir)
        digit_ex_fulldir = pathjoin(project.projdir_path, project.digit_exemplars_outdir)
        precinctnums_fullpath = pathjoin(project.projdir_path, project.precinctnums_outpath)
        if not os.path.exists(extracted_digitpatches_fulldir):
            print "Extracting Digit Patches..."
            _t = time.time()
            # TODO: Add progress bar here
            patch2temp = do_extract_digitbased_patches(self.project,
                                                       GRP_MODE_ALL_BALLOTS_NUM,
                                                       GRP_MODE_ALL_BALLOTS_NUM_MIN,
                                                       GRP_MODE_ALL_BALLOTS_NUM_MAX)
            print "...Finished Extracting Digit Patches ({0} s).".format(time.time() - _t)
            pickle.dump(patch2temp, open(pathjoin(project.projdir_path,
                                                  project.digitpatch2temp),
                                         'wb'))
        imgpaths = []
        for dirpath, dirnames, filenames in os.walk(extracted_digitpatches_fulldir):
            for imgname in [f for f in filenames if util_gui.is_image_ext(f)]:
                imgpaths.append(os.path.join(dirpath, imgname))

        self.mainpanel = DigitMainPanel(self, imgpaths,
                                        digit_ex_fulldir,
                                        precinctnums_fullpath,
                                        ondone=self.ondone)
        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.sizer.Add(self.mainpanel, proportion=1, flag=wx.EXPAND)
        self.SetSizer(self.sizer)

        statefile = pathjoin(self.project.projdir_path,
                             self.project.labeldigitstate)
        self.statefile=statefile
        self.mainpanel.start(statefile=statefile)
        self._hookfn = lambda: self.mainpanel.digitpanel.save_session(statefile=statefile)
        self.project.addCloseEvent(self._hookfn)

        self.Layout()

    def stop(self):
        if not self.project:
            # We haven't been run before, perhaps because this election
            # has no digit-based attributes.
            return
        self.mainpanel.digitpanel.save_session(statefile=self.statefile)
        self.project.removeCloseEvent(self._hookfn)
        self.export_results()

    def export_results(self):
        self.mainpanel.export_results()
        self.mainpanel.digitpanel.compute_and_save_digitexemplars_map()

    def ondone(self, results):
        """ Called when the user is finished labeling digit-based
        attributes.
        Input:
            dict results: maps {str patchpath: str precinct number}
        """
        print "Done Labeling Digit-Based Attributes"

    def invoke_sanity_checks(self, *args, **kwargs):
        return [self.check_digitstring_lengths()]

    def check_digitstring_lengths(self):
        """ Ensure that all digit patches have the correct number of
        labeled digits.
        """
        cnt_bad = self.mainpanel.digitpanel.get_num_bad_digitstrings()
        if cnt_bad == 0:
            return (True, True, "", 0, None)
        else:
            num_digits = get_num_digits(self.project)
            return (False, True, "{0} image patches do not have all \
digits labeled. Each image patch must have {1} digits present.\n\n\
Tip: Click the 'Sort' button to quickly see which patches still have \
missing digits. This will sort the image patches by number of labeled \
digits present, in increasing order.".format(cnt_bad, num_digits),
                    0, None)

class DigitMainPanel(wx.Panel):
    """A ScrolledPanel that contains both the DigitLabelPanel, and a
    simple button tool bar.
    """
    def __init__(self, parent, imgpaths,
                 digit_exemplars_outdir='digit_exemplars',
                 precinctnums_outpath='precinct_nums.txt',
                 ondone=None,
                 *args, **kwargs):
        wx.Panel.__init__(self, parent, *args, **kwargs)
        self.parent = parent

        self.button_sort = wx.Button(self, label="Sort")
        self.button_sort.Bind(wx.EVT_BUTTON, self.onButton_sort)
        self.button_done = wx.Button(self, label="I'm Done.")
        self.button_done.Bind(wx.EVT_BUTTON, self.onButton_done)
        self.button_done.Hide() # Just hide this for convenience
        btn_zoomin = wx.Button(self, label="Zoom In.")
        btn_zoomin.Bind(wx.EVT_BUTTON, self.onButton_zoomin)
        btn_zoomout = wx.Button(self, label="Zoom Out.")
        btn_zoomout.Bind(wx.EVT_BUTTON, self.onButton_zoomout)
	self.reset_button = wx.Button(self, label="Reset")
	self.reset_button.Bind(wx.EVT_BUTTON, self.onButton_reset)
        self.digitpanel = DigitLabelPanel(self, imgpaths,
                                          digit_exemplars_outdir,
                                          precinctnums_outpath,
                                          ondone)

        sizerbtns = wx.BoxSizer(wx.HORIZONTAL)
        sizerbtns.Add(self.button_sort)
        sizerbtns.Add((20,20))
        sizerbtns.Add(self.button_done)
        sizerbtns.Add((20,20))
        sizerbtns.Add(btn_zoomin)
        sizerbtns.Add((20,20))
        sizerbtns.Add(btn_zoomout)
        sizerbtns.Add((20,20))
        sizerbtns.Add(self.reset_button)
        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.sizer.Add(sizerbtns, border=10, flag=wx.ALL)
        self.sizer.Add(self.digitpanel, border=10, proportion=1, flag=wx.EXPAND | wx.ALL)
        self.SetSizer(self.sizer)
        self.Layout()

    def start(self, statefile=None):
        if not self.digitpanel.restore_session(statefile=statefile):
            self.digitpanel.start()
        self.Layout()

    def export_results(self):
        self.digitpanel.export_results()

    def onButton_sort(self, evt):
        # TODO: Add a progress bar for this, as this takes a nontrivial
        #       amount of time on large elections.
        self.digitpanel.sort_cells()

    def onButton_done(self, evt):
        self.digitpanel.on_done()

    def onButton_reset(self, evt):
	self.digitpanel.reset()    

    def onButton_zoomin(self, evt):
        dlg = wx.MessageDialog(self, message="Not implemented yet.")
        self.Disable()
        dlg.ShowModal()
        self.Enable()

    def onButton_zoomout(self, evt):
        dlg = wx.MessageDialog(self, message="Not implemented yet.")
        self.Disable()
        dlg.ShowModal()
        self.Enable()

class DigitLabelPanel(wx.lib.scrolledpanel.ScrolledPanel):
    MAX_WIDTH = 200
    # Per page
    NUM_COLS = 4
    NUM_ROWS = 3
    DIGITTEMPMATCH_JOB_ID = util.GaugeID('DigitTempMatchID')
    # Temp image files that we currently use.
    PATCH_TMP = '_patch_tmp.png'
    REGION_TMP = '_region_tmp.png'

    STATE_FILE = '_digitlabelstate.p'

    def __init__(self, parent,
                 imgpaths,
                 digit_exemplars_outdir='digit_exemplars',
                 precinctnums_outpath='precinct_nums.txt',
                 ondone=None, *args, **kwargs):
        """
        list imgpaths: List of imagepaths to display.
        str digit_exemplars_outdir: Directory in which we'll save each
                                    digit exemplar patch.
        fn ondone: A callback function to call when the digit-labeling is
                   finished. It should accept the results, which is a dict:
                       {str patchpath: str precinct number}
        """
        wx.lib.scrolledpanel.ScrolledPanel.__init__(self, parent, *args, **kwargs)
        self.parent = parent
        self.imgpaths = imgpaths
        self.digit_exemplars_outdir = digit_exemplars_outdir
        self.precinctnums_outpath = precinctnums_outpath  # TODO: NOT USED

        self.ondone = ondone

        # Keeps track of the currently-being-labeled digit
        self.current_digit = None
        # maps {str regionpath: list of (patchpath, matchID, digit, score, y1,y2,x1,x2, rszFac)
        self.matches = {}

        # self.PATCH2REGION: maps {str patchpath: str regionpath}
        self.patch2region = {}

        # maps {str regionpath: MyStaticBitmap obj}
        self.cells = {}
        # maps {str regionpath: StaticText txt}
        self.precinct_txts = {}

        self.sizer = wx.BoxSizer(wx.VERTICAL)

        self.gridsizer = wx.GridSizer(rows=DigitLabelPanel.NUM_ROWS, cols=DigitLabelPanel.NUM_COLS)
        #self.sizer.Add(self.gridsizer, proportion=1, flag=wx.EXPAND)
        self.sizer.Add(self.gridsizer, proportion=1, flag=wx.EXPAND)

        self.cellw, self.cellh = DigitLabelPanel.MAX_WIDTH, None

        self.rszFac = None
        
        self.i, self.j = 0, 0    # Keeps track of all boxes
        self.i_cur, self.j_cur = 0, 0  # Keeps track of currently
                                       # displayed boxes

        self.imgID2cell = {} # Maps {str imgID: (i,j)}
        self.cell2imgID = {} # Maps {(i,j): str imgID}

        self._box = None # A Box that is being created

        self.Bind(wx.EVT_CHILD_FOCUS, self.onChildFocus)

        self.SetSizer(self.sizer)

        self.Layout()
        self.gridsizer.Layout()
        self.SetupScrolling()

    def onChildFocus(self, evt):
        # If I don't override this child focus event, then wx will
        # reset the scrollbars at extremely annoying times. Weird.
        # For inspiration, see:
        #    http://wxpython-users.1045709.n5.nabble.com/ScrolledPanel-mouse-click-resets-scrollbars-td2335368.html
        pass

    def start(self):
        self.setup_grid()
        self.Layout()
        self.gridsizer.Layout()
        self.SetupScrolling()
        self.Refresh()
        self.Layout()
        self.gridsizer.Layout()

    def restore_session(self, statefile=None):
        """ Tries to restore the state from a previous session If it
        can't restore the state, then returns False. If this happens,
        you should call set.start(). Otherwise, returns True.
        """
        if statefile == None:
            statefile = DigitLabelPanel.STATE_FILE
        if not os.path.exists(statefile):
            return False

        state = pickle.load(open(statefile, 'rb'))
        self.matches = state['matches']
        self.patch2region = state['patch2region']
        cell_boxes = state['cell_boxes']
        digits = state['digits']
        self.start()
        for regionpath, digits_str in digits.iteritems():
            i, j = self.imgID2cell[regionpath]
            k = (self.NUM_COLS * i) + j
            self.precinct_txts[regionpath].SetLabel("{0} Precinct Number: {1}".format(str(k),
                                                                                       digits_str))
        #for regionpath, boxes in cell_boxes.iteritems():
        #    self.cells[regionpath].boxes = boxes
        # For awhile, a bug happened where self.matches could become 
        # out-of-sync with self.cells. This code will ensure that they
        # stay synced.
        def get_digit(patchpath):
            """ patchpaths are of the form:
                <projdir>/digit_exemplars/0_examples/*.png
            """
            return os.path.split(os.path.split(patchpath)[0])[1].split("_")[0]
        for regionpath, matches in self.matches.iteritems():
            boxes = []
            for (patchpath, matchID, digit, score, y1,y2,x1,x2,rszFac) in matches:
                x1, y1, x2, y2 = map(lambda c: int(round((c/rszFac))), (x1,y1,x2,y2))
                # Then, scale it by the resizing done in setup_grid
                x1, y1, x2, y2 = map(lambda c: int(round((c/self.rszFac))), (x1,y1,x2,y2))
                digit = get_digit(patchpath)
                box = Box(x1,y1,x2,y2,digit=digit)
                boxes.append(box)
            self.cells[regionpath].boxes = boxes
        return True

    def save_session(self, statefile=None):
        """ Saves the current session state. """
        if statefile == None:
            statefile = DigitLabelPanel.STATE_FILE
        f = open(statefile, 'wb')
        state = {}
        state['matches'] = self.matches
        state['patch2region'] = self.patch2region
        cell_boxes = {}
        digits = {} # maps regionpath to digits
        for regionpath, cell in self.cells.iteritems():
            cell_boxes[regionpath] = cell.boxes
            digits[regionpath] = cell.get_digits()
        state['cell_boxes'] = cell_boxes
        state['digits'] = digits
        pickle.dump(state, f)
        f.close()

    def _get_cur_loc(self):
        """Returns (x,y) of next cell location """
        return (self.j_cur * self.cellw, self.i_cur * self.cellh)

    def add_img(self, imgbitmap, imgID, npimg, imgpath, rszFac):
        """Adds a new image to this grid. Populates the self.imgID2cell,
        self.cell2imgID, self.i, self.j, self.cells, and 
        self.precinct_txts instance variables.
        """
        #(x, y) = self._get_cur_loc()
        assert imgID not in self.imgID2cell
        assert (self.i, self.j) not in self.cell2imgID
        self.imgID2cell[imgID] = (self.i, self.j)
        self.cell2imgID[(self.i, self.j)] = imgID
        x = self.j * self.cellw
        y = self.i * self.cellh
        if self.j >= (DigitLabelPanel.NUM_COLS - 1):
            self.i += 1
            self.j = 0
        else:
            self.j += 1
        w, h = imgbitmap.GetSize()
        s = wx.BoxSizer(wx.VERTICAL)
        txt = wx.StaticText(self, label="Precinct Number:")
        staticbitmap = MyStaticBitmap(self, self.i, self.j, imgpath, bitmap=imgbitmap, npimg=npimg, rszFac=rszFac)
        s.Add(txt)
        s.Add(staticbitmap, proportion=1, flag=wx.EXPAND)
        assert imgpath not in self.cells
        assert imgpath not in self.precinct_txts
        self.cells[imgpath] = staticbitmap
        self.precinct_txts[imgpath] = txt
        self.gridsizer.Add(staticbitmap)
        self.gridsizer.Add(s, border=10, flag=wx.ALL)

    def setup_grid(self, sorted=False,sorted_patches=None):
        """Reads in the digit patches (given by self.imgpaths)
        and displays them on a grid.
        """
        #w, h = self.GetClientSize()
        #w_suggested = int(round(w / self.NUM_COLS))
        print self.GetClientSize()
        print self.parent.GetClientSize()
        w_suggested = 400

        self.MAX_WIDTH = w_suggested
        self.cell_w = w_suggested

        # TODO: The following code block from here until the end of the
        # function can take a /long/ time (and consume quite a bit of
        # memory, >7 GB on Orange) on large elections. 
        def add_patches(imgpath):
            npimg = np.asarray(cv.LoadImageM(imgpath, cv.CV_LOAD_IMAGE_GRAYSCALE))
            w, h = npimg.shape[1], npimg.shape[0]
            c = float(w) / self.MAX_WIDTH
            w_scaled, h_scaled = int(self.MAX_WIDTH), int(round(h / c))
            if self.cellh == None:
                self.cellh = h_scaled
            if self.rszFac == None:
                self.rszFac = c
            npimg_rsz = fastResize(npimg, w_scaled)
            b = util.np2wxBitmap(npimg_rsz)
            self.add_img(b, imgpath, npimg_rsz, imgpath, c)

        if sorted == True:
            for imgname in sorted_patches:
                add_patches(imgname,'')
        else:
            for imgpath in self.imgpaths:
                add_patches(imgpath)
        
        print 'num images:', len(self.imgID2cell)
        self.Refresh()

    def update_precinct_txt(self, imgpath):
        """ Updates the 'Precinct Num:' StaticText. """
        txt = self.precinct_txts[imgpath]
        cell = self.cells[imgpath]
        i, j = self.imgID2cell[imgpath]
        k = (self.NUM_COLS * i) + j
        txt.SetLabel("{0} Precinct Number: {1}".format(str(k), cell.get_digits()))

    def start_tempmatch(self, imgpatch, cell):
        """ The user has selected a digit (imgpatch). Now we want to
        run template matching on all cells. """
        scipy.misc.imsave(self.PATCH_TMP, imgpatch)
        dlg = LabelDigitDialog(self, caption="What digit is this?",
                               labels=("Digit?:",),
                               imgpath=self.PATCH_TMP)
        self.Disable()
        self.disable_cells()
        retstat = dlg.ShowModal()
        self.Enable()
        self.enable_cells()
        if retstat == wx.ID_CANCEL:
            return
        digitval = dlg.results["Digit?:"]
        if digitval == None or digitval == '':
            d = wx.MessageDialog(self, message="You must enter in the \
digit.")
            self.Disable(); self.disable_cells()
            d.ShowModal()
            self.Enable(); self.enable_cells()
            return
        self.current_digit = digitval

        self.queue = Queue.Queue()
        t = ThreadDoTempMatch(imgpatch, self.imgpaths, self.queue, self.DIGITTEMPMATCH_JOB_ID)
        gauge = util.MyGauge(self, 1, thread=t, ondone=self.on_tempmatchdone,
                             msg="Finding digit instances...",
                             job_id=self.DIGITTEMPMATCH_JOB_ID)
        t.start()
        gauge.Show()

    def on_tempmatchdone(self):
        """Called when the template-matching thread is finished. 
        TODO: This makes the assumption that a GroupClass representing
        a digit-based attribute will have a grouplabel whose kv-pairs
        has a key 'digit', and its value is a digit ('0','1',etc.).
        This seems to unnecessarily restrict the architecture to only
        allowing one digit-based attribute in an election.
        """
        queue = self.queue
        exemplar_img = queue.get()
        matches = queue.get()

        matches_prune = prune_matches(matches, self.matches)
        # TODO: Doesn't prune away close-matches within the results of
        #       template matching.

        print "Number of matches pruned: {0}".format(len(matches) - len(matches_prune))
        matches = matches_prune
        
        if not matches:
            print "Couldn't find any matches."
            return
        print "Num. Matches Found:", len(matches)

        self.overlaymaps = {} # maps {int matchID: (i,j)}

        imgpatch = shared.standardImread(self.PATCH_TMP, flatten=True)
        h, w = imgpatch.shape

        global matchID
        matchID = get_last_matchID(self.digit_exemplars_outdir)
        imgpaths = []
        # regionpath is an attrpatch, not the blank ballot itself
        for (regionpath,score1,score2,Ireg,y1,y2,x1,x2,rszFac) in matches:
            rootdir = os.path.join(self.digit_exemplars_outdir, '{0}_examples'.format(self.current_digit))
            util_gui.create_dirs(rootdir)
            patchpath = os.path.join(rootdir, '{0}_match.png'.format(matchID))
            bb = map(lambda c: int(round(c / rszFac)), (y1,y2,x1,x2))
            Ireg = np.nan_to_num(Ireg)
            Ireg = shared.fastResize(Ireg, 1 / rszFac)
            scipy.misc.imsave(patchpath, Ireg)
            imgpaths.append(patchpath)
            self.matches.setdefault(regionpath, []).append((patchpath, matchID, self.current_digit, score2, y1, y2, x1, x2, rszFac))
            self.patch2region[patchpath] = regionpath
            matchID += 1

        exemplar_imgpath = self.PATCH_TMP

        # == Now, verify the found-matches via overlay-verification
        self.f = verify_overlays_new.CheckImageEqualsFrame(self, imgpaths, exemplar_imgpath, self.on_verifydone)
        self.f.Maximize()
        self.Disable()
        self.disable_cells()
        self.f.Show()

    def on_verifydone(self, verify_results):
        """Invoked once the user has finished verifying the template
        matching on the current digit. Add all 'correct' matches to
        the relevant cell's boxes.
        Input:
            dict VERIFY_RESULTS: maps {tag: [patchpath_i, ...]}
        """
        self.f.Close()
        self.Enable()
        self.enable_cells()
        # 1.) Remove all matches from self.matches that the user said
        # was not relevant, during overlay verification
        YES = verify_overlays_new.CheckImageEquals.TAG_YES
        NO = verify_overlays_new.CheckImageEquals.TAG_NO
        for tag, patchpaths in verify_results.iteritems():
            if tag == NO:
                # The user said that these elements are not relevant
                for patchpath in patchpaths:
                    regionpath = self.patch2region.pop(patchpath)
                    os.remove(patchpath)
                    # stuff[i] := (patchpath, matchID, digit, score, y1,y2,x1,x2, rszFac)
                    stuff = self.matches[regionpath]
                    stuff = [t for t in stuff if t[0] != patchpath]
                    self.matches[regionpath] = stuff

        # 2.) Add all matches that the user said was 'Good' to the UI
        added_matches = 0

        def get_digit(patchpath):
            """ patchpaths are of the form:
                <projdir>/digit_exemplars/0_examples/*.png
            """
            return os.path.split(os.path.split(patchpath)[0])[1].split("_")[0]
        for regionpath, stuff in self.matches.iteritems():
            boxes = []
            for (patchpath, matchID, digit, score, y1, y2, x1, x2, rszFac) in stuff:
                x1, y1, x2, y2 = map(lambda c: int(round((c/rszFac))), (x1,y1,x2,y2))
                # Then, scale it by the resizing done in setup_grid
                # (these coords are only for the LabelDigits UI).
                _x1, _y1, _x2, _y2 = map(lambda c: int(round((c/self.rszFac))), (x1,y1,x2,y2))
                dig = get_digit(patchpath)
                newbox = Box(_x1, _y1, _x2, _y2, digit=dig)
                added_matches += 1
                boxes.append(newbox)
                #self.add_box(newbox, regionpath)
            self.cells[regionpath].boxes = boxes
            self.update_precinct_txt(regionpath)
        print "Added {0} matches.".format(added_matches)
    
    def reset(self):
        """ resets the labelling state and digit ui """
        self.current_digit = None
        self.matches = {}   
        self.cells = {}
        self.precinct_txts = {}
        self.cellw, self.cellh = DigitLabelPanel.MAX_WIDTH, None
        self.rszFac = None
        self.i, self.j = 0, 0 
        self.i_cur, self.j_cur = 0, 0
        self.imgID2cell = {} 
        self.cell2imgID = {} 
        self._box = None 
            
        # reset the UI

        self.gridsizer.Clear(deleteWindows=True)
        self.setup_grid()
        self.gridsizer.Layout()

    def sort_cells(self):
        """ Sorts by strlen of the precinct digit string, the cells with the
        shortest digit strings will be displayed first """
        self.Disable()

        # Make sure the precinct txts are up to date.
        for regionpath, stuff in self.matches.iteritems():
            self.update_precinct_txt(regionpath)

        patch2precincts = self.get_patch2precinct().items()
        # Filter out the case where the precinct string is just the label
        # 'Precinct Number' instead of an empty string
        for x in patch2precincts:
            if x[1] == 'Precinct Number':
                loc = patch2precincts.index(x)
                patch2precincts[loc] = (x[0],'')

        sorted_patches = sorted(patch2precincts, key=lambda x: len(x[1]))
        sorted_patches = [x[0] for x in sorted_patches]

        # Reset instance variables. Consider integrating this into reset method when it is created.
        self.i, self.j = 0, 0    # Keeps track of all boxes
        self.i_cur, self.j_cur = 0, 0  # Keeps track of currently display boxes
        self.imgID2cell = {}
        self.cell2imgID = {}
        self.cells = {}
        self.precinct_txts = {}

        self.gridsizer.Clear(deleteWindows=True)
        self.setup_grid(sorted=True,sorted_patches=sorted_patches)
        
        def get_digit(patchpath):
            """ patchpaths are of the form:
                <projdir>/digit_exemplars/0_examples/*.png
            """
            return os.path.split(os.path.split(patchpath)[0])[1].split("_")[0]
        
        # Add digit bounding boxes to the UI
        for regionpath, matches in self.matches.iteritems():
            boxes = []
            for (patchpath, matchID, digit, score, y1,y2,x1,x2,rszFac) in matches:
                x1, y1, x2, y2 = map(lambda c: int(round((c/rszFac))), (x1,y1,x2,y2))
                # Then, scale it by the resizing done in setup_grid
                x1, y1, x2, y2 = map(lambda c: int(round((c/self.rszFac))), (x1,y1,x2,y2))
                digit = get_digit(patchpath)
                box = Box(x1,y1,x2,y2,digit=digit)
                boxes.append(box)
            self.cells[regionpath].boxes = boxes

        digits = {}
        
        # Set the Precinct Text labels
        for regionpath, cell in self.cells.iteritems():
            digits[regionpath] = cell.get_digits()

        for regionpath, digits_str in digits.iteritems():
            i, j = self.imgID2cell[regionpath]
            k = (self.NUM_COLS * i) + j
            self.precinct_txts[regionpath].SetLabel("{0} Precinct Number: {1}".format(str(k),
                                                                                       digits_str))
        
        self.gridsizer.Layout()
        self.Enable()
                   
    def compute_and_save_digitexemplars_map(self):
        digitexemplars_map = {} # maps {str digit: ((regionpath_i, score, bb, patchpath_i), ...)}
        for regionpath, stuff in self.matches.iteritems():
            for (patchpath, matchID, digit, score, y1, y2, x1, x2, rszFac) in stuff:
                bb = map(lambda c: int(round(c / rszFac)), (y1,y2,x1,x2))
                digitexemplars_map.setdefault(digit, []).append((regionpath, score, bb, patchpath))
        de_mapP = pathjoin(self.parent.parent.project.projdir_path,
                           self.parent.parent.project.digit_exemplars_map)
        pickle.dump(digitexemplars_map, open(de_mapP, 'wb'))
    
    def get_num_bad_digitstrings(self):
        """ Invoked when the user clicks the "I'm done" button:
        Make sure that len(all digit strings) == number user specified.
        Returns the number of digit strings that are not of the specified
        digitstring length.
        """
        # Make sure the precinct txts are up to date.
        for regionpath, stuff in self.matches.iteritems():
            self.update_precinct_txt(regionpath)

        # dict PATCH2PRECINCT: {str digitpatchpath: str digitstring}
        patch2precinct = self.get_patch2precinct()

        num_digits = get_num_digits(self.parent.parent.project)
        cnt_bad = 0
        for patchpath, digitstring in patch2precinct.iteritems():
            if len(digitstring) != num_digits:
                cnt_bad += 1
        return cnt_bad

    def on_done(self):
        """When the user decides that he/she has indeed finished
        labeling all digits. Export the results, such as the
        mapping from precinct-patch to precinct number.
        """
        # Check if all the precinct strings have the correct number of digits
        if self.get_num_bad_digitstrings() != 0:
            msg = 'Please check all digits have been matched. OpenCount has detected that some strings\
are not of proper length.' 
            dlg = wx.MessageDialog(self, message=msg, style=wx.OK)
            dlg.ShowModal()
        else:
            result = self.export_results()
            self.compute_and_save_digitexemplars_map()
            if self.ondone:
                self.ondone(result)
    
            self.Disable()

    def export_results(self):
        """ Saves out the digitattrvals_blanks.p file. """
        result = self.get_patch2precinct()
        self.export_precinct_nums(result)
        return result
    
    def get_patch2cellID(self):
        """ Return dictionary mapping patchpath to the cell ID on the digit UI """
        result = {}
        for patchpath, txt in self.precinct_txts.iteritems():
            assert patchpath not in result
            result[patchpath] = txt.GetLabel().split(' ')[0]
        
        return result

    def get_patch2precinct(self):
        """ Called by on_done, sort_cells, and check_digit_strings. Computes the result dictionary:
            {str patchpath: str precinct number},
        where patchpath is the path to the precinct patch of
        some blank ballot.
        """
        result = {}
        for patchpath, txt in self.precinct_txts.iteritems():
            assert patchpath not in result
            # txt.GetLabel() returns something like 'Precinct Number:0013038',
            # so get rid of this.
            digitstr = txt.GetLabel().split(":")[1].strip()
            result[patchpath] = digitstr
        return result

    def export_precinct_nums(self, result):
        """ Export precinct nums to a specified outfile. Saves a data
        structure dict of the form:
            {str blankpath: {attrtype: (str digitval, (y1,y2,x1,x2), int side)}}
        Input:
            dict result: maps {str patchpath: str digitval}
            str outpath:
        """
        proj = self.parent.parent.project  # TODO: breach of abstraction
        digitpatch2temp = pickle.load(open(pathjoin(proj.projdir_path,
                                                    proj.digitpatch2temp),
                                           'rb'))
        digitattrvals_blanks = {}  # maps {str templatepath: {digitattrtype: digitval}}
        for patchpath, digitval in result.iteritems():
            if patchpath not in digitpatch2temp:
                print "Uhoh, patchpath not in digitpatch2temp:", patchpath
                pdb.set_trace()
            temppath, attrstr, bb, side = digitpatch2temp[patchpath]
            digitattrvals_blanks.setdefault(temppath, {})[attrstr] = (digitval, bb, side)
        pickle.dump(digitattrvals_blanks, open(pathjoin(proj.projdir_path,
                                                        proj.digitattrvals_blanks),
                                               'wb'))

    def add_box(self, box, regionpath):
        assert regionpath in self.matches
        assert regionpath in self.cells
        self.cells[regionpath].add_box(box)

    def enable_cells(self):
        for cell in self.cells.values():
            cell.Enable()
    def disable_cells(self):
        for cell in self.cells.values():
            cell.Disable()

class MyStaticBitmap(wx.Panel):
    def __init__(self, parent, i, j, imgpath, bitmap=None, npimg=None, rszFac=1.0, *args, **kwargs):
        wx.Panel.__init__(self, parent, *args, **kwargs)
        self.parent = parent
        self.imgpath = imgpath
        self.rszFac = rszFac
        if not bitmap:
            bitmap = wx.EmptyBitmap(50, 50, -1)
        self.bitmap = bitmap
        self.npimg = npimg
        self.i, self.j = i, j
        self.boxes = []
        self._box = None

        self.SetMinSize(bitmap.GetSize())

        self.Bind(wx.EVT_LEFT_DOWN, self.onLeftDown)
        self.Bind(wx.EVT_LEFT_UP, self.onLeftUp)
        self.Bind(wx.EVT_MOTION, self.onMotion)
        self.Bind(wx.EVT_PAINT, self.onPaint)

    def cell2xy(self, i, j):
        return (self.parent.cellw * j, self.parent.cellh * i)

    def get_digits(self):
        """ Returns (in L-R order) the digits of all currently-labeled
        boxes.
        """
        sortedboxes = sorted(self.boxes, key=lambda b: b.x1)
        digits = ''
        for box in sortedboxes:
            if box.digit:
                digits += box.digit
        return digits

    def _start_box(self, x, y):
        assert not self._box
        self._box = Box(x, y, x+1, y+1)
    def _finish_box(self, x, y):
        assert self._box
        if self._box.width < 4 or self._box.height < 4:
            self._box = None
            return None
        tmp = self._box
        self._box = None
        # cut off coords that are out-of-bounds
        x1,y1,x2,y2 = Box.make_canonical(tmp)
        tmp.x1 = max(0, x1)
        tmp.y1 = max(0, y1)
        tmp.x2 = min(self.npimg.shape[1]-1, x2)
        tmp.y2 = min(self.npimg.shape[0]-1, y2)
        return tmp
    def _update_box(self, x, y):
        assert self._box
        self._box.x2, self._box.y2 = x, y

    def add_box(self, box):
        assert box not in self.boxes
        self.boxes.append(box)

    def onLeftDown(self, evt):
        x, y = evt.GetPosition()
        self._start_box(x, y)
        self.Refresh()
    def onLeftUp(self, evt):
        x, y = evt.GetPosition()
        box = self._finish_box(x, y)
        if box:
            # do template matching
            npimg = self.extract_region(box)
            if len(npimg.shape) == 1:
                print "Degenerate array returned from extract_region. \
Saving npimg as _errtmp_npimg_degenerate.png"
                scipy.misc.imsave("_errtmp_npimg_degenerate.png", npimg)
                return
            h, w = npimg.shape
            if w <= 2 or h <= 2:
                print "Extracted region was too small for template \
matching. Saving to: _errtmp_npimg.png"
                scipy.misc.imsave("_errtmp_npimg.png", npimg)
                return
            #npimg_crop = autocrop_img(npimg)
            # Let's try not cropping, since it might help with digit
            # recognition.
            npimg_crop = npimg 
            if npimg_crop == None:
                print "autocrop failed. saving to: _errtmp_npimg_failcrop.png"
                scipy.misc.imsave("_errtmp_npimg_failcrop.png", npimg)
                return
            #scipy.misc.imsave('before_crop.png', npimg)
            #scipy.misc.imsave('after_crop.png', npimg_crop)
            self.parent.start_tempmatch(npimg_crop, self)
        self.Refresh()
    def onMotion(self, evt):
        x, y = evt.GetPosition()
        if self._box and evt.LeftIsDown():
            self._update_box(x, y)
            self.Refresh()

    def extract_region(self, box):
        """Extracts box from the currently-displayed image. """
        coords = Box.make_canonical(box)
        #pilimg = util_gui.WxBitmapToPilImage(self.bitmap)
        #npimg = scipy.misc.imread(self.imgpath, flatten=True)
        npimg = shared.standardImread_v2(self.imgpath, flatten=True)
        x1,y1,x2,y2=map(lambda n: int(round(n*self.rszFac)),coords)
        return npimg[y1:y2, x1:x2]

    def onPaint(self, evt):
        """ Refresh screen. """
        if self.IsDoubleBuffered():
            dc = wx.PaintDC(self)
        else:
            dc = wx.BufferedPaintDC(self)
        dc.DrawBitmap(self.bitmap, 0, 0)
        self._draw_boxes(dc)
        evt.Skip()
        
    def _draw_boxes(self, dc):
        dc.SetBrush(wx.TRANSPARENT_BRUSH)
        dc.SetPen(wx.Pen("Green", 2))
        for box in self.boxes:
            x1, y1, x2, y2 = Box.make_canonical(box)
            dc.DrawRectangle(x1, y1, box.width, box.height)
        # Draw box-in-progress
        if self._box:
            dc.SetPen(wx.Pen("Red", 2))
            x1, y1, x2, y2 = Box.make_canonical(self._box)
            dc.DrawRectangle(x1, y1, self._box.width, self._box.height)        

class ThreadDoTempMatch(threading.Thread):
    def __init__(self, img1, imgpaths, queue, job_id, *args, **kwargs):
        """ Search for img1 within images in imgpaths. """
        threading.Thread.__init__(self, *args, **kwargs)
        self.img1 = img1
        self.imgpaths = imgpaths

        self.queue = queue
        self.job_id = job_id
        
    def run(self):
        h, w =  self.img1.shape
        bb = [0, h-1, 0, w-1]
        regions = []
        #wx.CallAfter(Publisher().sendMessage, "signals.MyGauge.nextjob", (numticks, self.job_id))
        for imgpath in self.imgpaths:
            regions.append(imgpath)
        try:
            matches = shared.find_patch_matchesV1(self.img1, bb[:], regions, threshold=0.8,
                                                  output_Ireg=True)
        except Exception as e:
            scipy.misc.imsave('_err_img1.png', self.img1)
            errf = open('_err_findpatchmatches.log', 'w')
            print >>errf, bb
            print >>errf, regions
            errf.close()
            traceback.print_exc()
            raise e
        print "DONE with temp matching. Found: {0} matches".format(len(matches))
        self.queue.put(self.img1)
        self.queue.put(matches)
        wx.CallAfter(Publisher().sendMessage, "signals.MyGauge.tick",
                     (self.job_id,))
        wx.CallAfter(Publisher().sendMessage, "signals.MyGauge.done",
                     (self.job_id,))

    def abort(self):
        print "Sorry, abort not implemented yet. :("

class LabelDigitDialog(common.TextInputDialog):
    def __init__(self, parent, imgpath=None, *args, **kwargs):
        common.TextInputDialog.__init__(self, parent, *args, **kwargs)
        img = wx.Image(imgpath, wx.BITMAP_TYPE_PNG) # assume PNG
        staticbitmap = wx.StaticBitmap(self, bitmap=wx.BitmapFromImage(img))
        self.sizer.Insert(1, staticbitmap, proportion=0)
        self.Fit()



class Box(object):
    def __init__(self, x1, y1, x2, y2, digit=None):
        self.x1, self.y1 = x1, y1
        self.x2, self.y2 = x2, y2
        self.digit = digit

    @property
    def width(self):
        return abs(self.x1 - self.x2)
    @property
    def height(self):
        return abs(self.y1 - self.y2)
    
    def set_coords(self, pts):
        self.x1, self.y1, self.x2, self.y2 = pts
    def get_coords(self):
        return self.x1, self.y1, self.x2, self.y2

    def __eq__(self, o):
        return (o and issubclass(type(o), Box) and
                self.x1 == o.x1 and self.y1 == o.y1 and
                self.x2 == o.x2 and self.y2 == o.y2 and
                self.digit == o.digit)

    @staticmethod
    def make_canonical(box):
        """ Takes two arbitrary (x,y) points and re-arranges them
        such that we get:
            (x_upperleft, y_upperleft, x_lowerright, y_lowerright)
        """
        xa, ya, xb, yb = box.get_coords()
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

    @staticmethod
    def is_overlap(box1, box2):
        """
        Returns True if any part of box1 is contained within box2
        Input:
            box1, box2
        """
        def is_within_box(pt, box):
            return box[0] < pt[0] < box[2] and box[1] < pt[1] < box[3]
        x1, y1, x2, y2 = Box.make_canonical(box1)
        rect1 = Box.make_canonical(box2)
        w, h = abs(x2-x1), abs(y2-y1)
        # Checks (in order): UL, UR, LR, LL corners
        return (is_within_box((x1,y1), rect1) or
                is_within_box((x1+w,y1), rect1) or 
                is_within_box((x1+w,y1+h), rect1) or 
                is_within_box((x1,y1+h), rect1))
    @staticmethod
    def too_close(box_a, box_b):
        """
        Input:
            box_a, box_b
        """
        dist = util_gui.dist_euclidean
        w, h = box_a.width, box_a.height
        (x1_a, y1_a, x2_a, y2_a) = Box.make_canonical(box_a)
        (x1_b, y1_b, x2_b, y2_b) = Box.make_canonical(box_b)
        return ((abs(x1_a - x1_b) <= w / 2.0 and
                 abs(y1_a - y1_b) <= h / 2.0) or
                Box.is_overlap(box_a, box_b) or 
                Box.is_overlap(box_b, box_a))

class DigitMainFrame(wx.Frame):
    """A frame that contains both the DigitLabelPanel, and a simple
    button toolbar.
    """
    def __init__(self, parent, imgpaths,
                 digit_exemplars_outdir='digit_exemplars',
                 precinctnums_outpath='precinct_nums.txt',
                 ondone=None,
                 *args, **kwargs):
        wx.Frame.__init__(self, parent, *args, **kwargs)
        self.parent = parent

        if not ondone:
            ondone = self.on_done

        self.mainpanel = DigitMainPanel(self, imgpaths,
                                        digit_exemplars_outdir,
                                        precinctnums_outpath,
                                        ondone)
        
        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.sizer.Add(self.mainpanel, border=10, proportion=1, flag=wx.EXPAND | wx.ALL)
        self.SetSizer(self.sizer)

    def start(self):
        self.Maximize()
        self.Show()
        self.Fit()
        self.mainpanel.start()

    def on_done(self, results):
        self.Close()

def prune_matches(matches, prev_matches):
    """ Discards matches that are already present within 'prev_matches'.
    This is if a match within matches has a bounding box that partially
    overlaps with a match in prev_matches.
    Input:
        lst matches: List of (regionpath,score1,score2,IReg,y1,y2,x1,x2,rszFac)
        dict prev_matches: maps {str regionpath: lst of (patchpath,matchID,score,y1,y2,x1,x2,rszFac)}
    Output:
        A new list of matches.
    """
    def is_overlap(bb1, bb2, c=0.50):
        """ Returns True if bb1 and bb2 share a certain amount of area.
        Input:
            bb1, bb2: tuple (y1, y2, x1, x2)
        """
        area_1 = float(abs(bb1[0]-bb1[1])*abs(bb1[2]-bb1[3]))
        common_area = float(get_common_area(bb1, bb2))
        overlap_area = common_area / area_1
        if overlap_area  >= c:
            return True
        else:
            return False
        return False
    def is_overlap_any(regionpath, bb, bb_lst, c=0.25):
        for regionpath2, bb2 in bb_lst:
            if regionpath == regionpath2 and is_overlap(bb, bb2, c=c):
                return True
        return False
    pruned_matches = []
    prev_bbs = []
    for regionpath, tuples in prev_matches.iteritems():
        for (patchpath, matchID, digit, score, y1, y2, x1, x2, rszFac) in tuples:
            prev_bbs.append((regionpath, (y1,y2,x1,x2)))
    for (regionpath,s1,s2,IReg,y1,y2,x1,x2,rszFac) in matches:
        if not is_overlap_any(regionpath, (y1,y2,x1,x2), prev_bbs):
            pruned_matches.append((regionpath,s1,s2,IReg,y1,y2,x1,x2,rszFac))
    return pruned_matches

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
            seg2 = seg1
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
    segh_a = y1a, y1a+h_a
    segw_b = x1b, x1b+w_b
    segh_b = y1b, y1b+h_b
    cseg_w = common_segment(segw_a, segw_b)
    cseg_h = common_segment(segh_a, segh_b)
    if cseg_w == None or cseg_h == None:
        return 0.0
    else:
        return abs(cseg_w[0]-cseg_w[1]) * abs(cseg_h[0]-cseg_h[1])
    '''
    if x1b < (x1a+w_a):
        x_segment = x1a+w_a - x1b
    else:
        x_segment = 0.0
    pdb.set_trace()
    if bb1[0] > bb2[0]:
        # Make bb1 on top of bb2
        tmp = bb1
        bb1 = bb2
        bb2 = tmp
    y1a,y2a,x1a,x2a = bb1
    y1b,y2b,x1b,x2b = bb2
    w_a, h_a = abs(x1a-x2a), abs(y1a-y2a)
    w_b, h_b = abs(x1b-x2b), abs(y1b-y2b)
    pdb.set_trace()
    if y1b < (y1a+h_a):
        y_segment = y1a+h_a - y1a
    else:
        y_segment = 0.0
    return x_segment * y_segment
    '''

def _test_get_common_area():
    bb1 = [2, 0, 0, 1]
    bb2 = [1, 0, 0, 2]
    print get_common_area(bb1, bb2)

    bb1 = [3, 1, 1, 2]
    bb2 = [2, 0, 3, 5]
    print get_common_area(bb1, bb2)

    bb1 = [1, 3, 1, 3]
    bb2 = [1, 3, 2, 3]
    print get_common_area(bb1, bb2)
#_test_get_common_area()
#pdb.set_trace()

def is_overlap(rect1, rect2):
    """
    Returns True if any part of rect1 is contained within rect2.
    Input:
        rect1: Tuple of (x1,y1,x2,y2)
        rect2: Tuple of (x1,y1,x2,y2)
    """
    def is_within_box(pt, box):
        return box[0] < pt[0] < box[2] and box[1] < pt[1] < box[3]
    x1, y1, x2, y2 = rect1
    w, h = abs(x2-x1), abs(y2-y1)
    # Checks (in order): UL, UR, LR, LL corners
    return (is_within_box((x1,y1), rect2) or
            is_within_box((x1+w,y1), rect2) or 
            is_within_box((x1+w,y1+h), rect2) or 
            is_within_box((x1,y1+h), rect2))
def too_close(b1, b2):
    """
    Input:
        b1: Tuple of (x1,y1,x2,y2)
        b2: Tuple of (x1,y1,x2,y2)
    """
    dist = util_gui.dist_euclidean
    w, h = abs(b1[0]-b1[2]), abs(b1[1]-b1[3])
    return ((abs(b1[0] - b2[0]) <= w / 2.0 and
             abs(b1[1] - b2[1]) <= h / 2.0) or
            is_overlap(b1, b2) or 
            is_overlap(b2, b1))

def autocrop_img(img):
    """ Given an image, try to find the bounding box. """
    def new_argwhere(a):
        """ Given an array, do what argwhere does but for 255, since
        np.argwhere does it for non-zero values instead.
        """
        b = a.copy()
        for i in range(b.shape[0]):
            for j in range(b.shape[1]):
                val = a[i,j]
                if val == 255:
                    b[i,j] = 0
                else:
                    b[i,j] = 1
        return np.argwhere(b)
    thresholded = util_gui.autothreshold_numpy(img, method='otsu')
    B = new_argwhere(thresholded)
    if len(B.shape) == 1:
        pdb.set_trace()
        return None
    (ystart, xstart), (ystop, xstop) = B.min(0), B.max(0) + 1
    return img[ystart:ystop, xstart:xstop]

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
            try:
                os.makedirs(pathjoin(outdir, attrs_sortedstr))
            except:
                pass
            outfilename = '{0}_{1}_exemplar.png'.format(idx, i)
            outfilepath = pathjoin(outdir,
                                   attrs_sortedstr,
                                   outfilename)
            cv.SaveImage(outfilepath, I)
            bb = (y1, y2, x1, x2)
            patch2temp[outfilepath] = (imgpath, attrs_sortedstr, bb, side)
            i += 1
    return patch2temp

def get_num_digits(proj):
    # list ATTRS: [dict attrbox_marsh, ...]
    attrs = pickle.load(open(proj.ballot_attributesfile))
    for attr in attrs:
        if attr['is_digitbased']:
            return attr['num_digits']
    raise Exception("Couldn't find any digit-based attributes?!")

def fastResize(I, w_new):
    """ Resizes a numpy image I to have width W_NEW. Maintains aspect ratio.
    Input:
        nparray I:
        int W_NEW:
    Output:
        nparray IOUT.
    """
    if I.shape[1] == w_new:
        return I
    Icv = cv.fromarray(I)
    h_new = int(round(I.shape[0] / (I.shape[1] / float(w_new))))
    I1cv = cv.CreateMat(h_new, int(w_new), Icv.type)
    if I.shape[1] >= w_new:
        cv.Resize(Icv, I1cv, interpolation=cv.CV_INTER_AREA)
    else:
        cv.Resize(Icv, I1cv, interpolation=cv.CV_INTER_CUBIC)
    Iout = np.asarray(I1cv)
    return Iout
    
def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("imgsdir", help="Input directory containing \
digit patches.")

    parser.add_argument("--limit", type=int, metavar="N",
                        help="Upper limit on images to display.")
    parser.add_argument("--increase", type=int, metavar="N",
                        help="Duplicates enough images in IMGSDIR so that \
there are N patches to label in the UI. Useful to test how scale-able the \
widget is.")
    return parser.parse_args()

def main():
    args = parse_args()
    imgsdir = args.imgsdir

    def read_imagepaths():
        imgpaths = []
        for dirpath, dirnames, filenames in os.walk(imgsdir):
            for imgname in [f for f in filenames if util_gui.is_image_ext(f)]:
                if args.limit and len(imgpaths) >= args.limit:
                    return imgpaths
                imgpaths.append(os.path.join(dirpath, imgname))
        return imgpaths

    imgpaths = read_imagepaths()

    # Note: The '--increase' option doesn't work in the current DigitsUI
    # implementation, as the widget assumes that input imagepaths are unique
    # (certain datastructures use imagepaths as keys)
    '''
    if args.increase and len(imgpaths) < args.increase:
        redund = int(math.ceil(float(args.increase - len(imgpaths)) / len(imgpaths)))
        imgpaths_cpy = imgpaths[:]
        i = 0
        while len(imgpaths) < args.increase:
            imgpaths.extend([imgpaths_cpy[i % len(imgpaths_cpy)]]*redund)
            i += 1
    '''
        
    print "(Info) Displaying {0} images.".format(len(imgpaths))
    app = wx.App(False)
    frame = DigitMainFrame(None, imgpaths)
    frame.start()
    app.MainLoop()

if __name__ == '__main__':
    main()

