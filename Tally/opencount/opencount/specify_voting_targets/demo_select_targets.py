import os, sys, pdb

import wx
sys.path.append('..')

from select_targets import *

"""
A Demo widget that is a much more compact version of the current
Select/Group Targets widget.
"""

class SelectTargetsPanel(ScrolledPanel):
    """ A widget that allows you to find voting targets on N ballot
    images.
    """
    TEMPLATE_MATCH_JOBID = 830

    def __init__(self, parent, *args, **kwargs):
        ScrolledPanel.__init__(self, parent, *args, **kwargs)
        self.parent = parent

        self.imgpaths = None
        # self.cur_i: Index of currently-displayed image (w.r.t self.IMGPATHS)
        self.cur_i = None

        # self.boxes: {int idx: [(x1, y1, x2, y2), ...]}
        self.boxes = {}

        self.toolbar = Toolbar(self)
        self.imagepanel = TemplateMatchDrawPanel(self, self.do_tempmatch)

        txt = wx.StaticText(self, label="Select all Voting Targets from \
this partition.")

        btn_next = wx.Button(self, label="Next Ballot")
        btn_prev = wx.Button(self, label="Previous Ballot")
        
        btn_next.Bind(wx.EVT_BUTTON, self.onButton_next)
        btn_prev.Bind(wx.EVT_BUTTON, self.onButton_prev)

        btn_sizer = wx.BoxSizer(wx.HORIZONTAL)
        btn_sizer.AddMany([(btn_prev,), (btn_next,)])
        
        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.sizer.Add(txt, flag=wx.ALIGN_CENTER)
        self.sizer.Add(self.toolbar, flag=wx.EXPAND)
        self.sizer.Add(self.imagepanel, proportion=1, flag=wx.EXPAND)
        self.sizer.Add(btn_sizer, flag=wx.ALIGN_CENTER)

        self.SetSizer(self.sizer)

    def start(self, imgpaths):
        self.imgpaths = imgpaths
        self.boxes = {}
        for i in xrange(len(self.imgpaths)):
            self.boxes[i] = []
        print "len(imgpaths):", len(imgpaths)

        self.display_image(0)

        #self.SetupScrolling()

    def do_tempmatch(self, box, img):
        """ Runs template matching on all of my self.IMGPATHS, using 
        the BOX from IMG as the template.
        Input:
            Box BOX:
            PIL IMG:
        """
        # 1.) Do an autofit.
        patch_prefit = img.crop((box.x1, box.y1, box.x2, box.y2))
        patch = util_gui.fit_image(patch_prefit, padx=0, pady=0)
        # 2.) Run template matching across all images in self.IMGPATHS,
        # using PATCH as the template.

        patch.save("_patch.png")
        
        queue = Queue.Queue()
        # Template match on /all/ images across all partitions, same page
        thread = TM_Thread(queue, self.TEMPLATE_MATCH_JOBID, patch, img, self.imgpaths, self.on_tempmatch_done)
        thread.start()

    def on_tempmatch_done(self, results, w, h):
        """ Invoked after template matching computation is complete. 
        Input:
            dict RESULTS: maps {str imgpath: [(x,y,score_i), ...}. The matches
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
        # 1.) Add the new matches to self.BOXES, but also filter out
        # any matches in RESULTS that are too close to previously-found
        # matches.
        for imgpath, matches in results.iteritems():
            print 'For imgpath {0}: {1} matches.'.format(imgpath, len(matches))
            imgpath_idx = self.imgpaths.index(imgpath)
            for (x, y, score) in matches:
                boxB = TargetBox(x, y, x+w, y+h)
                # 1.a.) See if any already-existing box is too close
                do_add = True
                for boxA in self.boxes[imgpath_idx]:
                    if too_close(boxA, boxB):
                        do_add = False
                        break
                if do_add:
                    self.boxes.setdefault(imgpath_idx, []).append(boxB)
        print 'Num boxes in current image:', len(self.boxes[self.cur_i])
        self.imagepanel.set_boxes(self.boxes[self.cur_i])
        self.Refresh()
        print "...Finished adding results from tempmatch run."

    def display_image(self, idx):
        """ Displays the image at IDX. Also handles reading/saving in
        the currently-created boxes for the old/new image.
        Input:
            int IDX: Index (into self.IMGPATHS) that you want to display.
        Output:
            Returns the IDX we decided to display, if successful.
        """
        if idx < 0 or idx >= len(self.imgpaths):
            print "Invalid idx into self.imgpaths:", idx
            pdb.set_trace()
        # 0.) Save boxes of old image
        '''
        if self.cur_i != None:
            self.boxes.setdefault(self.cur_i, []).extend(self.imagepanel.boxes)
        '''
        self.cur_i = idx
        imgpath = self.imgpaths[self.cur_i]
        
        # 1.) Display New Image
        print "...Displaying image:", imgpath
        wximg = wx.Image(imgpath, wx.BITMAP_TYPE_ANY)
        # 1.a.) Resize image s.t. width is equal to containing width
        wP, hP = self.parent.GetSize()
        _c = wximg.GetWidth() / float(wP)
        wimg = wP
        himg = int(round(wximg.GetHeight() / _c))
        self.imagepanel.set_image(wximg, size=(wimg, himg))
        
        # 2.) Read in previously-created boxes for IDX (if exists)
        boxes = self.boxes.get(self.cur_i, [])
        self.imagepanel.set_boxes(boxes)

        #self.SetupScrolling()
        self.Refresh()
        return idx

    def display_next(self):
        """ Displays the next image in self.IMGPATHS. If the end of the
        list is reached, returns None, and does nothing. Else, returns
        the new image index.
        """
        next_idx = self.cur_i + 1
        if next_idx >= len(self.imgpaths):
            return None
        return self.display_image(next_idx)
        
    def display_prev(self):
        prev_idx = self.cur_i - 1
        if prev_idx < 0:
            return None
        return self.display_image(prev_idx)

    def onButton_next(self, evt):
        self.display_next()
    def onButton_prev(self, evt):
        self.display_prev()
    def zoomin(self, amt=0.1):
        self.imagepanel.zoomin(amt=amt)
        #self.SetupScrolling()
    def zoomout(self, amt=0.1):
        self.imagepanel.zoomout(amt=amt)
        #self.SetupScrolling()

class Toolbar(wx.Panel):
    def __init__(self, parent, *args, **kwargs):
        wx.Panel.__init__(self, parent, *args, **kwargs)
        self.parent = parent
        
        self._setup_ui()
        self._setup_evts()
        self.Layout()

    def _setup_ui(self):
        self.btn_addtarget = wx.Button(self, label="Add Target...")
        self.btn_modify = wx.Button(self, label="Modify...")
        self.btn_zoomin = wx.Button(self, label="Zoom In...")
        self.btn_zoomout = wx.Button(self, label="Zoom Out...")
        self.sizer = wx.BoxSizer(wx.VERTICAL)
        btn_sizer = wx.BoxSizer(wx.HORIZONTAL)
        btn_sizer.AddMany([(self.btn_addtarget,), (self.btn_modify,),
                           (self.btn_zoomin,), (self.btn_zoomout,)])
        self.sizer.Add(btn_sizer)
        self.SetSizer(self.sizer)

    def _setup_evts(self):
        self.btn_addtarget.Bind(wx.EVT_BUTTON, lambda evt: self.setmode(BoxDrawPanel.M_CREATE))
        self.btn_modify.Bind(wx.EVT_BUTTON, lambda evt: self.setmode(BoxDrawPanel.M_IDLE))
        self.btn_zoomin.Bind(wx.EVT_BUTTON, lambda evt: self.parent.zoomin())
        self.btn_zoomout.Bind(wx.EVT_BUTTON, lambda evt: self.parent.zoomout())
    def setmode(self, mode_m):
        self.parent.imagepanel.set_mode_m(mode_m)

def main():
    class TestFrame(wx.Frame):
        def __init__(self, parent, imgpaths, *args, **kwargs):
            wx.Frame.__init__(self, parent, size=(800, 900), *args, **kwargs)
            self.parent = parent
            self.imgpaths = imgpaths

            self.st_panel = SelectTargetsPanel(self)
            self.st_panel.start(imgpaths)

    args = sys.argv[1:]
    imgsdir = args[0]
    imgpaths = []
    for dirpath, _, filenames in os.walk(imgsdir):
        for imgname in [f for f in filenames if isimgext(f)]:
            imgpaths.append(os.path.join(dirpath, imgname))
    app = wx.App(False)
    f = TestFrame(None, imgpaths)
    f.Show()
    app.MainLoop()

if __name__ == '__main__':
    main()
