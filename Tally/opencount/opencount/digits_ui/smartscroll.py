import sys, os, time, pdb, traceback, math, argparse, threading, Queue, textwrap
import wx, numpy as np, cv
from wx.lib.scrolledpanel import ScrolledPanel

"""
TODO: It's still not quite as fast as I'd like it to be. Memory efficient,
but a bit slow when scrolling. My guesses:

--  The Thread prefetcher has a memory leak -- images are not getting
    correctly evicted, causing memory usage to increase unbounded a bit.

Not sure if prefetching is actually helping /that/ much in terms of
UI responsiveness.

Activation time is still noticeable when crossing page boundaries.
In particular, much time is spent in the ImagePanel.configure_me method,
which does image resizings. The breakdown between get_img and configure_me
is roughly 30% vs. 70%.

Maybe, during prefetching, the resizing can also be done?
"""

# Flags for ImagePanel modes
CREATE = 0
IDLE = 1

class SmartScrolledGridPanel(ScrolledPanel):
    """ A widget that displays a scrollable grid of images. Internally, the
    implementation should be able to handle large numbers of images.
    """
    def __init__(self, parent, *args, **kwargs):
        ScrolledPanel.__init__(self, parent, *args, **kwargs)
        
        self.imgpath2cellid = None
        self.cellid2imgpath = None

        self.page2cellids = None
        self.cellid2page = None

        # set CELLIDS_MANUAL: Stores the cellids that were manually labeled
        # by the user.
        self.cellids_manual = None

        # tuple PAGESIZE: (int rows, int cols)
        self.pagesize = None
        self.pages_active = None
        self.pages_inactive = None

        self.cellsize, self.cellsize_orig = None, None

        # dict CELLID2BOXES: {int cellid: [[int x1, y1, x2, y2, str val], ...]}
        #     A box with None as the coordinates is a box that was manually
        #     labeled by the user, e.g. [None, None, None, None, '2'].
        self.cellid2boxes = None 

        # list PANELS_POOL: [Panel_0, ...]
        self.panels_pool = None

        self.scale = 1.0
        self.lookahead = None
        self.DO_PREFETCH = None
        self.num_pages_total = None
        
        # MODE: One of CREATE, IDLE. Controls behavior of the cells
        self.mode = IDLE

        self.colors = None

        self.t_loadimgs = None
        
        #self.Bind(wx.EVT_SCROLLWIN, self.onScroll)
        for evt in (wx.EVT_SCROLLWIN_TOP,
                    wx.EVT_SCROLLWIN_BOTTOM,
                    wx.EVT_SCROLLWIN_LINEUP,
                    wx.EVT_SCROLLWIN_LINEDOWN,
                    wx.EVT_SCROLLWIN_PAGEUP,
                    wx.EVT_SCROLLWIN_PAGEDOWN):
            self.Bind(evt, lambda evt: self.onScroll(evt, pos=self.CalcUnscrolledPosition((0,0)), isScrollPos=False))
        for evt in (wx.EVT_SCROLLWIN_THUMBTRACK,
                    wx.EVT_SCROLLWIN_THUMBRELEASE):
            self.Bind(evt, lambda evt: self.onScroll(evt, pos=evt.GetPosition(), isScrollPos=True))

        self.Bind(wx.EVT_MOUSEWHEEL, self.onMouseWheel)
        self.Bind(wx.EVT_CHILD_FOCUS, self.onChildFocus)
        self.Bind(wx.EVT_WINDOW_DESTROY, self.Close)

    def get_state(self):
        """ Outputs current state as a dictionary. """
        return {'imgpath2cellid': self.imgpath2cellid,
                'cellid2imgpath': self.cellid2imgpath,
                'page2cellids': self.page2cellids,
                'cellid2page': self.cellid2page,
                'pagesize': self.pagesize,
                'cellsize': self.cellsize,
                'cellsize_orig': self.cellsize_orig,
                'cellid2boxes': self.cellid2boxes,
                'lookahead': self.lookahead,
                'DO_PREFETCH': self.DO_PREFETCH,
                'colors': self.colors,
                'num_pages_total': self.num_pages_total,
                'cellids_manual': self.cellids_manual}
    def restore_state(self, state):
        """ Given a state dict (in the form of get_state()), restore the state. """
        for name, val in state.iteritems():
            setattr(self, name, val)

        # Legacy handling
        if self.cellids_manual == None:
            self.cellids_manual = set()

        self.pages_active, self.pages_inactive = set(), set()
        self.panels_pool = []

        # Pre-mark all pages as inactive
        for pageidx in self.page2cellids.keys():
            self.pages_inactive.add(pageidx)

        # Start off our thread friend
        if self.DO_PREFETCH:
            print "(SmartScroll) Prefetching images with separate thread."
            self.t_loadimgs = LoadImagesThread()
        else:
            print "(SmartScroll) Not prefetching (DO_PREFETCH was False)"
            self.t_loadimgs = DummyThread()
        self.t_loadimgs.start()

        # Populate sizer with dummy pages at first
        self.sizer = wx.BoxSizer(wx.VERTICAL)
        dummy_spacer = (self.pagesize[1] * self.cellsize[0], self.pagesize[0] * self.cellsize[1])
        for pageidx in self.pages_inactive:
            self.sizer.Add(dummy_spacer)
        self.SetSizer(self.sizer)
        self.Layout()

        # Pre-populate the self.panels_pool with the appropriate number
        # of panels.
        num_activecells_max = (2*self.lookahead + 1) * self.pagesize[0] * self.pagesize[1]
        for _ in xrange(num_activecells_max):
            self.panels_pool.append(ImagePanel(self, color="red", size=self.cellsize))
        
        x_amt, y_amt = self.cellsize[0]/10, self.cellsize[1]/10
        self.SetupScrolling(scroll_x=True, scroll_y=True, rate_x=x_amt, rate_y=y_amt)

        # Activate the first few pages
        for pageidx in xrange(self.lookahead + 1):
            self.activate_page(pageidx)

        self.Layout()

    def Close(self, evt):
        if self.t_loadimgs != None:
            self.t_loadimgs.stop_me()
        evt.Skip()

    def onChildFocus(self, evt):
        # If I don't override this child focus event, then wx will
        # reset the scrollbars at extremely annoying times. Weird.
        # For inspiration, see:
        #    http://wxpython-users.1045709.n5.nabble.com/ScrolledPanel-mouse-click-resets-scrollbars-td2335368.html
        pass

    def set_mode(self, mode):
        """ Sets the mode behavior for my ImagePanels. Should be
        one of CREATE, IDLE.
        """
        if mode not in (CREATE, IDLE):
            print "(SmartScroll) Invalid mode passed to set_mode:", mode
            return
        self.mode = mode
        self.update_cursor()

    def update_cursor(self):
        """ Updates the mouse pointer based on current state. """
        if self.mode == CREATE:
            cursor = wx.StockCursor(wx.CURSOR_CROSS)
        elif self.mode == IDLE:
            cursor = wx.StockCursor(wx.CURSOR_ARROW)
        else:
            cursor = wx.StockCursor(wx.CURSOR_ARROW)
        # Set the cursor for all active ImagePanels
        for idx_page, item_page in enumerate([s for s in self.sizer.GetChildren()]):
            if item_page.IsSpacer():
                # This is a dummy inactive page -- replace with a resized spacer
                continue
            sizer_page = item_page.GetSizer() # This is an active page
            for sizer_row in [s.GetSizer() for s in sizer_page.GetChildren()]:
                for i, item in enumerate(sizer_row.GetChildren()):
                    if item.IsSpacer():
                        # This is a dummy-spacer
                        continue
                    elif item.IsWindow():
                        # This is an ImagePanel
                        item.GetWindow().SetCursor(cursor)

    def start(self, imgpaths, cellsize=(100, 50), colors=('red', 'blue', 'green', 'white', 'black'),
              num_cols=4,
              rows_page=10, lookahead=1,
              DO_PREFETCH=True):
        """ Display K cells of size SIZE, alternating colors COLORS.
        Input:
            tuple IMGPATHS:
                If a list element is None, then we will create a dummy cell.
                Useful for dev purposes. Imgpaths must be unique.
            tuple SIZE:
            tuple COLORS:
            int PAGE_ROWS:
                Sets how many rows a single page contains
            int LOOKAHEAD:
                Sets how many pages to load ahead/before the current viewing window.
                Must be >= 1.
            bool DO_PREFETCH:
                If True, then run a separate thread that tries to load images
                ahead of time, to make UI more responsive.
        """
        self.DO_PREFETCH = DO_PREFETCH

        self.pagesize = (rows_page, num_cols)
        self.cellsize = cellsize
        self.cellsize_orig = cellsize # Keep track of this for rescaling purposes
        self.lookahead = lookahead

        self.colors = colors # Only used for dummy panels

        self.imgpath2cellid, self.cellid2imgpath = {}, {}
        self.page2cellids = {} # {int pageidx: [int cellid_0, ...]}
        self.cellid2page = {} # {int cellid: int pageidx}
        self.pages_active, self.pages_inactive = set(), set()
        self.cellid2boxes = {}
        self.panels_pool = []

        self.cellids_manual = set()

        # Start off our thread friend
        if self.DO_PREFETCH:
            print "(SmartScroll) Prefetching images with separate thread."
            self.t_loadimgs = LoadImagesThread()
        else:
            print "(SmartScroll) Not prefetching (DO_PREFETCH was False)"
            self.t_loadimgs = DummyThread()
        self.t_loadimgs.start()

        dummy_idx = 0
        for i, imgpath in enumerate(imgpaths):
            if imgpath == None:
                # TODO: Crashes will happen if you mix dummy cells with
                #       "normal" cells.
                imgpath = dummy_idx
                dummy_idx += 1
            cur_row = int(math.floor(i / float(num_cols)))
            cur_page = int(math.floor(cur_row / float(self.pagesize[0])))
            self.imgpath2cellid[imgpath] = i
            self.cellid2imgpath[i] = imgpath
            self.page2cellids.setdefault(cur_page, []).append(i)
            self.cellid2page[i] = cur_page
            self.pages_inactive.add(cur_page)

        # Populate sizer with dummy pages at first
        self.sizer = wx.BoxSizer(wx.VERTICAL)
        dummy_spacer = (self.pagesize[1] * self.cellsize[0], self.pagesize[0] * self.cellsize[1])
        for pageidx in self.pages_inactive:
            self.sizer.Add(dummy_spacer)
        self.SetSizer(self.sizer)
        self.Layout()

        # Pre-populate the self.panels_pool with the appropriate number
        # of panels.
        num_activecells_max = (2*self.lookahead + 1) * self.pagesize[0] * self.pagesize[1]
        for _ in xrange(num_activecells_max):
            self.panels_pool.append(ImagePanel(self, color="red", size=self.cellsize))
        
        self.num_pages_total = len(self.pages_inactive)

        x_amt, y_amt = self.cellsize[0]/10, self.cellsize[1]/10
        self.SetupScrolling(scroll_x=True, scroll_y=True, rate_x=x_amt, rate_y=y_amt)

        # Activate the first few pages
        for pageidx in xrange(self.lookahead + 1):
            self.activate_page(pageidx)

        self.Layout()

    def on_box_create(self, cellid, box, npimg, label=None):
        """ Called by child ImagePanel when the user creates a new box.
        Input:
            int CELLID:
            list BOX: [int x1, y1, x2, y2]
            nparray NPIMG:
                The image that the user drew the BOX on.
            str LABEL:
        """
        box.append(label)
        self.add_cell_box(cellid, box)
    def on_box_delete(self, cellid, box, npimg):
        """ Called by child ImagePanel when the user deletesa  box.
        Input:
            int CELLID:
            list BOX: [int x1, y1, x2, y2]
            nparray NPIMG:
        """
        self.remove_cell_box(cellid, box)

    def get_page_status(self, pageidx):
        """ Returns True if page is active, False o.w. """
        return pageidx in self.pages_active

    def get_panel(self):
        """ First check if self.panels_pool has any panels that exist.
        If an available one exists, then remove it from the pool and
        return it. Otherwise, create a new one. This machinery is to
        allow us to re-use widgets, to speed up UI.
        """
        if self.panels_pool:
            panel = self.panels_pool.pop()
        else:
            panel = ImagePanel(self, color="red")
        return panel
    def recycle_panel(self, panel):
        self.panels_pool.append(panel)

    def get_image(self, imgpath):
        """ Load in image IMGPATH. We ask our special thread friend, in
        case we asked for it in the past.
        """
        return self.t_loadimgs.read_and_release_img(imgpath)
        
    def activate_page(self, pageidx):
        """ Activate page at PAGEIDX.
        Input:
            int PAGEIDX:
        """
        if self.get_page_status(pageidx):
            print "(SmartScroll) page '{0}' is already active.".format(pageidx)
            return # Page is already active
        if pageidx < 0 or pageidx >= self.num_pages_total:
            return
        cellids = self.page2cellids[pageidx]
        panels = []
        for cellid in cellids:
            t_total = time.time()
            imgpath = self.cellid2imgpath[cellid]
            if type(imgpath) == int:
                clr = self.colors[imgpath % len(self.colors)]
                panel = self.get_panel()
                panel.configure_me(cellid=cellid, color=clr, text="Page={0}".format(pageidx), size=self.cellsize)
            else:
                # TODO: Handle reading in images.
                panel = self.get_panel()
                t = time.time()
                npimg = self.get_image(imgpath)
                dur_getimg= time.time() - t
                # Assumes that each cell is the same size.
                text = "Image:{0}".format(os.path.split(imgpath)[1])
                t = time.time()
                panel.configure_me(cellid=cellid, npimg=npimg, text=text, size=self.cellsize)
                dur_config = time.time() - t
            panels.append(panel)
            dur_total = time.time() - t_total
            #print "(Total): {0:.6f}s".format(dur_total)
            #print "    GetImg: {0:.5f}%".format(0.0 if dur_total == 0 else (100.0 * (dur_getimg / float(dur_total))))
            #print "    Config: {0:.5f}%".format(0.0 if dur_total == 0 else (100.0 * (dur_config / float(dur_total))))

        sizer_page = wx.BoxSizer(wx.VERTICAL)
        for row in xrange(self.pagesize[0]):
            sizer_row = wx.BoxSizer(wx.HORIZONTAL)
            for col in xrange(self.pagesize[1]):
                idx = (row * self.pagesize[1]) + col
                if idx >= len(panels):
                    # This row is incomplete -- that's ok, just fill it
                    # with dummy space.
                    panel = self.cellsize
                else:
                    panel = panels[idx]
                sizer_row.Add(panel)
            sizer_page.Add(sizer_row)
        
        # Kick out the dummy spacer standing in for PAGEIDX
        self.sizer.Detach(pageidx)
        self.sizer.Insert(pageidx, sizer_page)
        self.pages_active.add(pageidx)
        self.pages_inactive.remove(pageidx)
        
    def deactivate_page(self, pageidx):
        """ Deactivate page at PAGEIDX, releasing held resources.
        Input:
            int PAGEIDX:
        """
        if not self.get_page_status(pageidx):
            print "(SmartScroll) page '{0}' is already deactivated.".format(pageidx)
            return # Page is already deactivated
        if pageidx < 0 or pageidx >= self.num_pages_total:
            return
        sizer_page = self.sizer.GetChildren()[pageidx].GetSizer()
        self.sizer.Detach(pageidx)
        for sizer_row in [s.GetSizer() for s in sizer_page.GetChildren()]:
            for panel in [p.GetWindow() for p in sizer_row.GetChildren() if p.IsWindow()]:
                self.recycle_panel(panel)
        sizer_page.Clear(deleteWindows=False)
        #sizer_page.Clear(deleteWindows=True)
        dummy_spacer = (self.pagesize[1] * self.cellsize[0], self.pagesize[0] * self.cellsize[1])
        self.sizer.Insert(pageidx, dummy_spacer)
        self.pages_active.remove(pageidx)
        self.pages_inactive.add(pageidx)

    def sort_cells(self):
        """ Rearranges the cells such that the cells with the fewest number
        of boxes are displayed first.
        """
        print "(SmartScroll) Sorting Cells..."
        # First, deactivate all active pages.
        for page in tuple(self.pages_active)[:]:
            self.deactivate_page(page)

        num2cellids = {} # {int num_boxes: [int cellid, ...]}
        for cellid in self.cellid2imgpath.keys():
            boxes = self.cellid2boxes.get(cellid, [])
            num2cellids.setdefault(len(boxes), []).append(cellid)
        i = 0
        num_rows, num_cols = self.pagesize
        # Reset current page setup, redefine the ordering.
        self.page2cellids = {}
        self.pages_active = set()
        self.pages_inactive = set()
        for num, cellids in sorted(num2cellids.iteritems()):
            for cellid in sorted(cellids):
                cur_row = int(math.floor(i / float(num_cols)))
                cur_page = int(math.floor(cur_row / float(num_rows)))
                self.page2cellids.setdefault(cur_page, []).append(cellid)
                self.cellid2page[cellid] = cur_page
                self.pages_inactive.add(cur_page)
                i += 1

        # TODO: This implementation ignores the user's current scroll location.
        #       It's not a big deal, as the user just has to scroll a bit for
        #       everything to come back -- might be a nice enhancement to tune this.

        # Activate the first few pages
        for pageidx in xrange(self.lookahead + 1):
            self.activate_page(pageidx)

        self.Layout()

    def mark_cell_manually(self, cellid, labels):
        """ Manually (explicitly) provide a label for a cell. This is useful
        if a cell is so fouled up that it can't be reasonably labeled via the
        template matching search (or as a last-resort).
        Input:
            int CELLID:
            tuple LABELS: (str label0, label1, ...). 
                Must have same length as self.NUM_OBJECTS, if NUM_OBJECTS != None.
        """
        if self.NUM_OBJECTS != None and len(labels) != self.NUM_OBJECTS:
            print "(SmartScroll) mark_cell_manually: Input labels has length {0}, must have length {1}: {2}".format(len(labels), self.NUM_OBJECTS, labels)
            return
        print "(SmartScroll) Marking cell {0} manually w/ label: {1}".format(cellid, labels)
        self.cellid2boxes[cellid] = [[None, None, None, None, label] for label in labels]
        self.cellids_manual.add(cellid)

    def get_cell_boxes(self, cellid):
        """ Return the boxes for the input CELLID. """
        return self.cellid2boxes.get(cellid, ())
    def add_cell_box(self, cellid, box):
        """
        Input:
            list BOX: [int x1, y1, x2, y2, str val]
        """
        self.cellid2boxes.setdefault(cellid, []).append(box)
    def remove_cell_box(self, cellid, box):
        self.cellid2boxes[cellid].remove(box)

    def check_pages(self, pos):
        """ Given the upperleft corner of the current viewing window POS,
        determine if any pages need to be evicted, and if any pages need
        to be read in.
        Input:
            tuple POS: (int X, int Y)
        Output:
            (list PAGES_TOLOAD, PAGES_TOEVICT)
        """
        pageidx_cur = self.pos2pageidx(pos)
        pageidxs = set(xrange(max(0, pageidx_cur - self.lookahead), min(self.num_pages_total, pageidx_cur + self.lookahead + 1)))
        to_load  = pageidxs.difference(self.pages_active)
        to_evict = self.pages_active.difference(pageidxs)
        return to_load, to_evict

    def pos2pageidx(self, pos):
        """ Given an unscrolled position POS, return the pageidx that POS
        lands on.
        Input:
            tuple POS: (int X, int Y)
        Output:
            int PAGEIDX
        """
        x, y = pos
        row_cur = int(math.floor(y / float(self.cellsize[1])))
        page_cur = int(math.floor(row_cur / float(self.pagesize[0])))
        return page_cur

    def rescale(self, newscale):
        """ Zoom in/out s.t. the self.scale = NEWSCALE. This will traverse
        all sizers, and enlarge the ImagePaneld/dummy-spacers appropriately.
        Additionally, this method will auto-scroll to the 'correct' position,
        so that the user doesn't lose his/her place.
        """
        w_new, h_new = int(round(self.cellsize_orig[0] * newscale)), int(round(self.cellsize_orig[1] * newscale))
        self.cellsize = (w_new, h_new)
        self.scale = newscale
        pagesize = (self.pagesize[1] * self.cellsize[0], self.pagesize[0] * self.cellsize[1])

        # self.sizer contains either BoxSizers (active pages) or dummyspacers (inactive pages)
        for idx_page, item_page in enumerate([s for s in self.sizer.GetChildren()]):
            if item_page.IsSpacer():
                # This is a dummy inactive page -- replace with a resized spacer
                try:
                    #self.sizer.Replace(idx_page, pagesize)
                    self.sizer.Remove(idx_page)
                    self.sizer.Insert(idx_page, pagesize)
                except:
                    traceback.print_exc()
                    pdb.set_trace()
                continue
            sizer_page = item_page.GetSizer() # This is an active page
            for sizer_row in [s.GetSizer() for s in sizer_page.GetChildren()]:
                for i, item in enumerate(sizer_row.GetChildren()):
                    if item.IsSpacer():
                        # This is a dummy-spacer -- replace this with a re-sized
                        # spacer
                        sizer_row.Remove(i)
                        sizer_row.Insert(i, self.cellsize)
                    elif item.IsWindow():
                        # This is an ImagePanel
                        item.GetWindow().resize_me(self.cellsize)
                    else:
                        print "WAT"
                        pdb.set_trace()
        self.Layout()

        # TODO: Re-scroll to return to previous location.

    def zoomin(self, amt=0.25):
        return self.rescale(self.scale + amt)
    def zoomout(self, amt=0.25):
        return self.rescale(self.scale - amt)
    
    def onScroll(self, evt, pos=None, isScrollPos=False):
        """
        Input:
            Event EVT:
            tuple POS: (int X, int Y)
                If ISSCROLLPOS is True, then POS is in scroll-units.
                Else, POS is in pixel (unscrolled) coordinates.
        """
        t_total = time.time()
        if not hasattr(self, 'scroll_evt_idx'):
            self.scroll_evt_idx = 0
        orient = evt.GetOrientation()

        if not isScrollPos:
            pos = pos
        else:
            x_rate, y_rate = self.GetScrollPixelsPerUnit()
            if orient == wx.HORIZONTAL:
                # TODO: HANDLE THIS CASE. Likely I'll have to have a 
                # statevar keeping track of the last Y scroll pos, yuck.
                # NOTE: Because this method returns if orient == wx.HORIZONTAL,
                #       this actually works, by dumb luck. Should I do the 'right'
                #       thing and fix this?
                pos = (0, pos * y_rate) # hack, totally wrong.
            else:
                pos = (0, pos * y_rate) # OK to 'ignore' X val, as we never use it.
                
        '''
        print "({0}) Scrolled: {1}".format(self.scroll_evt_idx, 'horiz' if orient == wx.HORIZONTAL else 'vert')
        print "        Position:", pos
        print "        Page:", self.pos2pageidx(pos)
        '''
        self.scroll_evt_idx += 1

        evt.Skip()
        
        if orient == wx.HORIZONTAL:
            return

        pages_toload, pages_toevict = self.check_pages(pos)
        flag_didchange = False
        t = time.time()
        for pageidx in sorted(pages_toevict):
            self.deactivate_page(pageidx)
            flag_didchange = True
        dur_evict = time.time() - t
        t = time.time()
        for pageidx in sorted(pages_toload):
            self.activate_page(pageidx)
            flag_didchange = True
        dur_activate = time.time() - t

        # Finally -- ask our thread friend to load images of prior/post pages
        # as a pre-fetching scheme, asynchronously
        t_threadask = time.time()
        cur_pageidx = self.pos2pageidx(pos)
        C = 1
        min_pageidx = max(0, cur_pageidx - self.lookahead - C)
        max_pageidx = min(self.num_pages_total, cur_pageidx + self.lookahead + C)
        pages_prefetch = tuple(xrange(min_pageidx, cur_pageidx - self.lookahead)) + tuple(xrange(cur_pageidx+1 + self.lookahead, max_pageidx))

        if pages_prefetch:
            for pageidx in sorted(pages_prefetch):
                cellids = self.page2cellids[pageidx]
                for cellid in cellids:
                    wx.CallAfter(self.t_loadimgs.request_img, self.cellid2imgpath[cellid])
        dur_threadask = time.time() - t_threadask
        t = time.time()
        if flag_didchange:
            self.Layout()
        dur_layout = time.time() - t
        dur_total = time.time() - t_total
        if dur_total >= 0.1:
            print "(Total): {0:.5f}s".format(dur_total)
            print "    Deactivate: {0:.4f}%".format(0.0 if dur_total == 0 else (100.0 * (dur_evict / float(dur_total))))
            print "    Activate: {0:.4f}%".format(0.0 if dur_total == 0 else (100.0 * (dur_activate / float(dur_total))))
            print "    ThreadAsk: {0:.4f}%".format(0.0 if dur_total == 0 else (100.0 * (dur_threadask / float(dur_total))))
            print "    Layout: {0:.4f}%".format(0.0 if dur_total == 0 else (100.0 * (dur_layout / float(dur_total))))
            print len(pages_prefetch), pages_prefetch, cur_pageidx

    def onMouseWheel(self, evt):
        # Mousewheel events lead to weird scrolling behavior! In particular,
        # the evt.GetPosition() output from ScrollWin events is always (0,0),
        # which is wrong. For now, ignore mousewheel scrolls.
        # Note: However, the current scroll implementation is fine with this
        #       quirk, so, I've re-enabled mousewheel scrolling.
        evt.Skip()

    def onScrollThumb(self, evt):
        # Scrolling by clicking+dragging the thumbwheel causes strange scroll
        # behavior for large scroll bars (i.e. when there are many elements).
        # No idea why, so, I've disabled it for now.
        # Note: Binding EVT_SCROLLWIN_THUMBTRACK + EVT_SCROLLWIN_THUMBRElEASE
        #       did not fix the problem (just made even stranger scroll quirks). Hm.
        pass

class ImagePanel(wx.Panel):
    def __init__(self, parent, cellid=None, color="red", npimg=None, text=None, size=(100, 50), *args, **kwargs):
        """ This widget can function either as a panel displaying an image, or as a 
        panel displaying a solid-color background.
        Input:
            int CELLID:
                Used to retrieve/update the parent's CELLID2BOXES data struct.
            str COLOR:
                Solid-color background to display.
            nparray NPIMG:
                Overrides the 'color' option.
            str TEXT:
                An optional text string to display.
            tuple SIZE: (int W, int H)
                Specify the size that this panel should take up. If this is
                displaying an image, then the image will be rescaled s.t. the
                widths match up (aspect ratio is maintained).
        """
        wx.Panel.__init__(self, parent, size=size, *args, **kwargs)
        self.cellid = cellid
        self.color = color
        self.npimg = npimg # Original-scale image
        self.scale = 1.0 # Determines what scale the image is displayed as.
        self.text = text
        self.size = size
        self.SetSize(self.size)

        self.bitmap = None

        # list BOX_CUR: [int x1, int y1, int x2, int y2]
        self.box_cur = None
        self.is_creating = False

        # list BOXES_SEL: [[int x1, y1, x2, y2], ...]
        self.boxes_sel = None
        self.is_selecting = False
        
        # list BOX_REGIONSEL: [int x1, y1, x2, y2], in UI coord system
        self.box_regionsel, self.is_regionselecting = None, False

        # Keeps track of previous mouse x/y coords for certain events
        self._x_prev, self._y_prev = None, None

        self.Bind(wx.EVT_PAINT, self.onPaint)
        self.Bind(wx.EVT_LEFT_DOWN, self.onLeftDown)
        self.Bind(wx.EVT_LEFT_UP, self.onLeftUp)
        self.Bind(wx.EVT_MOTION, self.onMotion)
        self.Bind(wx.EVT_KEY_DOWN, self.onKeyDown)

        self.popup_menu = wx.Menu()
        m_viewcontext = self.popup_menu.Append(-1, "View Image Context...")
        m_labelmanual = self.popup_menu.Append(-1, "Manually Label.../Undo Manual Label")
        m_printpath   = self.popup_menu.Append(-1, "(Dev) Print This Patch Path")

        self.Bind(wx.EVT_MENU, lambda evt: self.view_image_context(), m_viewcontext)
        self.Bind(wx.EVT_MENU, self.onMenu_manual_label, m_labelmanual)
        self.Bind(wx.EVT_MENU, self.onMenu_printpath, m_printpath)

        self.Bind(wx.EVT_CONTEXT_MENU, self.onShowPopup)

        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.SetSizer(self.sizer)

        self.configure_me(cellid=self.cellid, color=self.color, npimg=self.npimg, text=self.text, size=self.size)

    def onMenu_printpath(self, evt):
        print self.GetParent().cellid2imgpath[self.cellid]

    def onShowPopup(self, evt):
        pos = self.ScreenToClient(evt.GetPosition())
        self.PopupMenu(self.popup_menu, pos)

    def view_image_context(self):
        """ Display a new window with the entire image displayed. """
        print "(ImagePanel) view_image_context"
        # TODO: Implement me. This should spawn a new wx.Frame with a
        #       ScrolledPanel whose background is the entire image.
        #       There should also be a zoomin/zoomout feature.
        wx.MessageDialog(self, message="Not implemented yet!").ShowModal()
        
    def onMenu_manual_label(self, evt):
        print "(ImagePanel) onMenu_manual_label"
        if self.cellid in self.GetParent().cellids_manual:
            print "(ImagePanel) undo_manual_label"
            self.GetParent().cellids_manual.remove(self.cellid)
            self.get_boxes()[:] = []
            self.Refresh()
            return

        dlg = ManualLabelDialog(self, self.GetParent().NUM_OBJECTS)
        status = dlg.ShowModal()
        if status == wx.ID_CANCEL:
            return
        labels = dlg.labels
        self.GetParent().mark_cell_manually(self.cellid, labels)
        self.Refresh()

    def configure_me(self, cellid=None, color="red", npimg=None, text=None, size=(100, 50)):
        self.cellid = cellid
        self.color = color
        self.npimg = npimg
        self.text = text
        self.size = size
        self.SetSize(self.size)
        self.sizer.Clear()
        self.sizer.Add((self.size))

        self.box_cur, self.is_creating = None, False
        self.boxes_sel, self.is_selecting = [], False
        self.box_regionsel, self.is_regionselecting = None, False

        if self.npimg != None:
            h, w = self.npimg.shape[0], self.npimg.shape[1]
            if w == self.size[0]:
                npimg_rsz = self.npimg
                self.scale = 1.0
            else:
                # Match the width of SIZE, maintaining aspect ratio
                w_new = self.size[0]
                h_new = int(round(h / (w / float(w_new))))
                self.scale = w / float(w_new)
                npimg_rsz = fastResize(self.npimg, w_new, h_new)
            npimg_rsz_rgb = npgray2rgb(npimg_rsz)
            self.bitmap = wx.BitmapFromImage(wx.ImageFromBuffer(npimg_rsz_rgb.shape[1], npimg_rsz_rgb.shape[0], npimg_rsz_rgb))
        else:
            self.bitmap = None
            self.scale = self.GetParent().cellsize_orig[0] / float(self.size[0])
        self.Refresh()
        self.Layout()

    def resize_me(self, size):
        """ Change my size. This will cause the image to be re-scaled.
        Input:
            tuple SIZE: (int W, int H)
        """
        self.size = size
        self.SetSize(size)
        self.sizer.Clear()
        self.sizer.Add(self.size)
        if self.npimg != None:
            h, w = self.npimg.shape[0], self.npimg.shape[1]
            if w == self.size[0]:
                npimg_rsz = self.npimg
                self.scale = 1.0
            else:
                # Match the width of SIZE, maintaining aspect ratio
                w_new = self.size[0]
                h_new = int(round(h / (w / float(w_new))))
                self.scale = w / float(w_new)
                npimg_rsz = fastResize(self.npimg, w_new, h_new)
            npimg_rsz_rgb = npgray2rgb(npimg_rsz)
            self.bitmap = wx.BitmapFromImage(wx.ImageFromBuffer(npimg_rsz_rgb.shape[1], npimg_rsz_rgb.shape[0], npimg_rsz_rgb))
        else:
            self.bitmap = None
            self.scale = self.GetParent().cellsize_orig[0] / float(self.size[0])
        self.Refresh()
        self.Layout()

    def get_boxes(self):
        # Note: Output box coords are in orig image coord system,
        #       i.e. they may need to be rescaled by self.scale
        return self.GetParent().get_cell_boxes(self.cellid)

    def get_mode(self):
        return self.GetParent().mode

    def set_mode(self, mode):
        """ 
        Input:
            int MODE: 
                Possible modes are:
                    -- CREATE
                    -- IDLE
        """
        if mode not in (CREATE, IDLE):
            print "Invalid mode passed:", mode
            return
        mode2cursor = {CREATE: wx.Cursor(wx.CURSOR_CROSS),
                       IDLE  : wx.Cursor(wx.CURSOR_ARROW)}
        self.SetCursor(mode2cursor[self.get_mode()])
        self.GetParent().set_mode(mode)

    def onLeftDown(self, evt):
        x, y = evt.GetPosition()
        self.SetFocus()
        if self.get_mode() == CREATE:
            if self.cellid in self.GetParent().cellids_manual:
                dlg = wx.MessageDialog(self, style=wx.OK,
                                       message="This cell has already been \
manually labeled. To undo this manual labeling, right-click this cell and \
choose the 'Undo Manual Label' option.")
                dlg.ShowModal()
                return
            self.box_cur = [x, y, x+1, y+1]
            self.is_creating = True
        elif self.get_mode() == IDLE:
            if self.get_boxes():
                ximg, yimg = self.c2img(x,y)
                box_sel = get_closest_box(self.get_boxes(), (ximg, yimg), mode='within')
                if box_sel:
                    self.is_selecting = True
                    if box_sel not in self.boxes_sel:
                        # Selecting a new box -- unselect all others
                        self.boxes_sel = [box_sel]
                else:
                    self.boxes_sel, self.is_selecting = [], False
                    self.box_regionsel, self.is_regionselecting = [x, y, x+1, y+1], True
            else:
                self.boxes_sel, self.is_selecting = [], False
                self.box_regionsel, self.is_regionselecting = [x, y, x+1, y+1], True

        self.Refresh()
        
    def onLeftUp(self, evt):
        x, y = evt.GetPosition()
        if self.is_creating:
            self.box_cur[2], self.box_cur[3] = x, y
            self.is_creating = False
            # Output boxes are in original image coord system
            box_out = list(canonicalize_box(self.c2img(*self.box_cur)))
            self.GetParent().on_box_create(self.cellid, box_out, self.npimg)
            self.box_cur = None
        elif self.is_regionselecting:
            box_region_canon = self.c2img(*canonicalize_box(self.box_regionsel))
            boxes = get_boxes_within(self.get_boxes(), box_region_canon)
            if boxes:
                self.boxes_sel, self.is_selecting = boxes, True
            self.box_regionsel, self.is_regionselecting = None, False
            
        self.Refresh()

    def onMotion(self, evt):
        x, y = evt.GetPosition()
        if self._x_prev == None:
            self._x_prev, self._y_prev = x, y # Safe default vals

        if self.is_creating and evt.LeftIsDown():
            self.box_cur[2], self.box_cur[3] = x, y
        elif self.is_selecting and evt.LeftIsDown():
            ximg, yimg = self.c2img(x,y)
            # TODO: Displace boxes, not set (x1,y1)
            xdelt, ydelt = self.c2img(x - self._x_prev, y - self._y_prev)
            for box in self.boxes_sel:
                box[:4] = box[0] + xdelt, box[1] + ydelt, box[2] + xdelt, box[3] + ydelt
        elif self.is_regionselecting and evt.LeftIsDown():
            self.box_regionsel[2:] = x, y

        self._x_prev, self._y_prev = x, y
        self.Refresh()
       
    def onKeyDown(self, evt):
        keycode = evt.GetKeyCode()
        if (keycode == wx.WXK_DELETE or keycode == wx.WXK_BACK):
            for box in self.boxes_sel:
                self.GetParent().on_box_delete(self.cellid, box, self.npimg)
            self.Refresh()
        elif ((keycode in (wx.WXK_UP, wx.WXK_DOWN, wx.WXK_LEFT, wx.WXK_RIGHT))
              and self.boxes_sel):
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
            for box in self.boxes_sel:
                box[0] += xdel_img
                box[1] += ydel_img
                box[2] += xdel_img
                box[3] += ydel_img
            self.Refresh()
 
    def c2img(self, *coords):
        """ Converts client (UI) coordinates to image coordinates. """
        return [int(round(coord * self.scale)) for coord in coords]
    def img2c(self, *coords):
        """ Converts image coordinates to client (UI) coordinates. """
        return [int(round(coord / self.scale)) for coord in coords]

    def draw_boxes(self, dc):
        """ Draws any boxes if necessary. """
        dc.SetBrush(wx.TRANSPARENT_BRUSH)
        if self.box_cur:
            dc.SetPen(wx.Pen("red", 3))
            box_canon = canonicalize_box(self.box_cur)
            w, h = box_canon[2] - box_canon[0], box_canon[3] - box_canon[1]
            dc.DrawRectangle(box_canon[0], box_canon[1], w, h)
        if self.box_regionsel:
            dc.SetPen(wx.Pen("black", 1))
            box_canon = canonicalize_box(self.box_regionsel)
            w, h = box_canon[2] - box_canon[0], box_canon[3] - box_canon[1]
            dc.DrawRectangle(box_canon[0], box_canon[1], w, h)

        dc.SetFont(wx.Font(12, wx.FONTFAMILY_TELETYPE, wx.FONTSTYLE_NORMAL, weight=wx.FONTWEIGHT_BOLD))
        dc.SetTextForeground("Blue")

        for box in self.GetParent().get_cell_boxes(self.cellid):
            if box[0] == None:
                # Signal for manual-label box
                continue
            if box in self.boxes_sel:
                dc.SetPen(wx.Pen("yellow", 3))
            else:
                dc.SetPen(wx.Pen("green", 2))                
            box_canon = canonicalize_box(box)
            # Correct for scaling
            box_canon = self.img2c(*box_canon[:4])
            w, h = box_canon[2] - box_canon[0], box_canon[3] - box_canon[1]
            dc.DrawRectangle(box_canon[0], box_canon[1], w, h)
            label = box[-1]
            if label != None:
                w_txt, h_txt = dc.GetTextExtent(label)
                x0 = box_canon[0]
                y0 = box_canon[1] - h_txt
                if y0 < 0:
                    y0 = box_canon[1] + h + 2
                dc.DrawText(label, x0, y0)
        
    def onPaint(self, evt):
        if self.IsDoubleBuffered():
            dc = wx.PaintDC(self)
        else:
            dc = wx.BufferedPaintDC(self)
        if self.bitmap != None:
            brush = wx.Brush(self.color, wx.TRANSPARENT)
            dc.SetBrush(brush)
            dc.DrawBitmap(self.bitmap, 0, 0)
        else:
            brush = wx.Brush(self.color, wx.SOLID)
            dc.SetBrush(brush)
            w, h = self.GetClientSize()
            dc.DrawRectangle(0, 0, w, h)
        
        if self.text != None:
            dc.SetFont(wx.Font(10, wx.FONTFAMILY_ROMAN, wx.FONTSTYLE_NORMAL, weight=wx.FONTWEIGHT_NORMAL))
            dc.SetTextForeground("Black")
            dc.DrawText(self.text, 5, 5)

        if self.GetParent().cellids_manual and self.cellid in self.GetParent().cellids_manual:
            dc.SetFont(wx.Font(12, wx.FONTFAMILY_TELETYPE, wx.FONTSTYLE_NORMAL, weight=wx.FONTWEIGHT_BOLD))
            dc.SetTextForeground("Blue")
            if self.text == None:
                x0, y0 = 5, 5
            else:
                w, h = dc.GetTextExtent(self.text)
                x0, y0 = 5, h + 5
            label = "".join([b[-1] for b in self.get_boxes()])
            dc.DrawText("Manual Label: {0}".format(label), x0, y0)
            dc.SetBrush(wx.Brush("Red", wx.TRANSPARENT))
            dc.SetPen(wx.Pen("Red", 8))
            dc.DrawRectangle(0, 0, self.size[0], self.size[1])
        else:
            self.draw_boxes(dc)
        
        return dc

class ManualLabelDialog(wx.Dialog):
    def __init__(self, parent, num_labels, *args, **kwargs):
        wx.Dialog.__init__(self, parent, title="Enter Label",
                           style=wx.CAPTION | wx.SYSTEM_MENU | wx.RESIZE_BORDER | wx.MAXIMIZE_BOX | wx.MINIMIZE_BOX,
                           *args, **kwargs)
        self.num_labels = num_labels
        self.labels = None
        
        txt = ["Please provide the label for this image by separating \
each letter/digit (i.e. the smallest unit) with a comma. For instance:",
               "    1,0,0,0,3,7"]
        txtwrap = "\n".join([textwrap.fill(t, 75) for t in txt])
        
        stxt_inst = wx.StaticText(self, label=txtwrap)

        stxt_label = wx.StaticText(self, label="Label: ")
        self.txtctrl = wx.TextCtrl(self, size=(200,-1), style=wx.TE_PROCESS_ENTER)
        self.txtctrl.Bind(wx.EVT_TEXT_ENTER, lambda evt: self.onButton_ok(None))

        sizer_input = wx.BoxSizer(wx.HORIZONTAL)
        sizer_input.AddMany([(stxt_label,), (self.txtctrl,)])

        btn_ok = wx.Button(self, label="Ok")
        btn_ok.Bind(wx.EVT_BUTTON, self.onButton_ok)
        btn_cancel = wx.Button(self, label="Cancel")
        btn_cancel.Bind(wx.EVT_BUTTON, lambda evt: self.EndModal(wx.ID_CANCEL))

        sizer_btns = wx.BoxSizer(wx.HORIZONTAL)
        sizer_btns.AddMany([(btn_ok,), ((10,0),), (btn_cancel,)])

        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.sizer.Add(stxt_inst, border=10, flag=wx.ALL)
        self.sizer.Add(sizer_input, border=10, flag=wx.ALIGN_CENTER | wx.ALL)
        self.sizer.Add(sizer_btns, border=10, flag=wx.ALIGN_CENTER | wx.ALL)
        
        self.SetSizer(self.sizer)
        self.Fit()

    def onButton_ok(self, evt):
        txt_user = self.txtctrl.GetValue()
        labels = txt_user.split(",")
        if self.num_labels != None and len(labels) != self.num_labels:
            wx.MessageDialog(self, style=wx.OK | wx.SYSTEM_MENU | wx.RESIZE_BORDER,
                             message="Invalid number of (comma-separated) labels \
entered. There must be {0} comma-separated labels -- you entered {1} labels.".format(self.num_labels, len(labels))).ShowModal()
            return
        
        self.labels = labels
        self.EndModal(wx.ID_OK)

def canonicalize_box(box):
    """ Takes two arbitrary (x,y) points and re-arranges them
    such that we get:
        (x_upperleft, y_upperleft, x_lowerright, y_lowerright)
    """
    (xa, ya, xb, yb), userdata = box[:4], tuple(box[4:])
    w, h = abs(xa - xb), abs(ya - yb)
    if xa < xb and ya < yb:
        # UpperLeft, LowerRight
        return (xa, ya, xb, yb) + userdata
    elif xa < xb and ya > yb:
        # LowerLeft, UpperRight
        return (xa, ya - h, xb, yb + h) + userdata
    elif xa > xb and ya < yb:
        # UpperRight, LowerLeft
        return (xa - w, ya, xb + w, yb) + userdata
    else:
        # LowerRight, UpperLeft
        return (xb, yb, xa, ya) + userdata

class DummyThread(object):
    """ A 'fake' thread that is used when DO_PREFETCH=False. """
    def stop_me(self): pass
    def request_img(self, imgpath): pass
    def read_and_release_img(self, imgpath):
        return np.asarray(cv.LoadImageM(imgpath, cv.CV_LOAD_IMAGE_GRAYSCALE))
    def start(self): pass

class LoadImagesThread(threading.Thread):
    """ A listener thread that will load in images asynchronously, to 
    make the UI a bit more responsive.
    """
    def __init__(self, *args, **kwargs):
        threading.Thread.__init__(self, *args, **kwargs)

        # dict IMGPATH2IMG: maps {str imgpath: nparray img}
        self.imgpath2img = {}
        self.queue_in = Queue.Queue()

        self.lock = threading.Lock() # protects self.imgpath2img

        self.stop_running = threading.Event()

    def stop_me(self):
        self.stop_running.set()

    def request_img(self, imgpath):
        """ Request this LoadImagesThread to fetch this image asynchronously. """
        self.queue_in.put(imgpath)

    def read_and_release_img(self, imgpath):
        """ Ask for an image IMGPATH. If IMGPATH is not held by this
        LoadImagesThread instance, then it will simply load it from
        disk and return it. Else, it will return it from its internal
        store and remove it from itself as well.
        """
        self.lock.acquire()
        if imgpath not in self.imgpath2img:
            npimg = np.asarray(cv.LoadImageM(imgpath, cv.CV_LOAD_IMAGE_GRAYSCALE))
        else:
            npimg = self.imgpath2img.pop(imgpath)
        self.lock.release()
        return npimg

    def _load_img(self, imgpath):
        self.lock.acquire()
        if imgpath not in self.imgpath2img:
            npimg = np.asarray(cv.LoadImageM(imgpath, cv.CV_LOAD_IMAGE_GRAYSCALE))
            self.imgpath2img[imgpath] = npimg
        self.lock.release()

    def run(self, *args, **kwargs):
        print "(LoadImagesThread) Listening..."
        while not self.stop_running.is_set():
            try:
                imgpath = self.queue_in.get(block=True, timeout=2)
                self._load_img(imgpath)
            except Queue.Empty:
                pass
    
def fastResize(I, w, h):
    """ 
    Input:
        obj I: numpy img
        int W, H:
    Output:
        A resized image Iout.
    """
    if I.shape[1] == w:
        return I
    Icv = cv.fromarray(I)
    I1cv=cv.CreateMat(int(h), int(w), Icv.type)
    if w < I.shape[1]:
        cv.Resize(Icv,I1cv,interpolation=cv.CV_INTER_AREA)
    else:
        cv.Resize(Icv, I1cv, interpolation=cv.CV_INTER_CUBIC)
    Iout = np.asarray(I1cv)
    return Iout

def npgray2rgb(npimg):
    if len(npimg.shape) == 3:
        return npimg
    npimg_out = np.zeros((npimg.shape[0], npimg.shape[1], 3), dtype=npimg.dtype)
    npimg_out[:,:,0] = npimg
    npimg_out[:,:,1] = npimg
    npimg_out[:,:,2] = npimg
    return npimg_out

def get_closest_box(boxes, pt, mode='within'):
    """ Returns the box in BOXES closest to PT.
    Input:
        list BOXES: [(int x1, y1, x2, y2, ...), ...]
        tuple PT: (int X, int Y)
    Output:
        list BOX: (int x1, y1, x2, y2, ...)
    """
    if not boxes:
        return None

    def is_pt_within(pt, box):
        return (pt[0] >= box[0] and pt[0] <= box[2] and
                pt[1] >= box[1] and pt[1] <= box[3])
    if mode == 'within':
        candidates = [b for b in boxes if is_pt_within(pt, b)]
        if not candidates:
            return None
        return get_closest_box(candidates, pt, mode='center')

    mode2fn = {'center': lambda b: ((b[2] + b[0]) / 2.0, (b[3] + b[1]) / 2.0),
               'upperleft': lambda b: (b[0], b[1])}
        
    distpairs = [(distL2(mode2fn[mode](box), pt), box) for box in boxes]
    return min(distpairs)[1]

def get_boxes_within(boxes, region):
    """ Returns all boxes in BOXES that are contained within the region
    REGION.
    Input:
        list BOXES: [(int x1, y1, x2, y2, *data), ...]
        list REGION: (x1, y1, x2, y2)
    Output:
        list BOXES_OUT.
    """
    def is_box_contained(b):
        return (b[0] >= region[0] and b[1] >= region[1] and
                b[2] <= region[2] and b[3] <= region[3])
    return [b for b in boxes if is_box_contained(b)]
    
def distL2(pt0, pt1):
    return math.sqrt((pt0[0] - pt1[0])**2.0 + (pt0[1] - pt1[1])**2.0)


"""
=============================
==== Demo/Dev code below ====
=============================
"""

class MainFrame(wx.Frame):
    def __init__(self, parent, imgpaths, rows_page, lookahead, num_cols, cell_size, no_prefetch, *args, **kwargs):
        wx.Frame.__init__(self, parent, size=(1000, 700), *args, **kwargs)
        self.imgpaths = imgpaths
        self.rows_page = rows_page
        self.lookahead = lookahead
        self.num_cols = num_cols
        self.cell_size = cell_size
        self.mainpanel = SmartScrolledGridPanel(self)
        
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

        self.mainpanel.start(imgpaths, rows_page=rows_page, lookahead=self.lookahead, num_cols=self.num_cols, cellsize=self.cell_size,
                             DO_PREFETCH=not no_prefetch)

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
    parser.add_argument("--k", type=int, metavar="K", default=2000,
                        help="Number of dummy grid cells to display.")
    parser.add_argument("--imgsdir", help="Directory of images to \
display. Overrides the '--k' option.")

    parser.add_argument("--limit", type=int, 
                        help="Upper limit of images to process.")

    parser.add_argument("--rows_page", type=int, metavar="N", default=4,
                        help="Number of rows per page.")
    parser.add_argument("--lookahead", type=int, metavar="C", default=2,
                        help="Set the lookahead parameter.")
    parser.add_argument("--num_cols", type=int, metavar="COLS", default=5,
                        help="Set the number of columns.")
    parser.add_argument("--cellsize", type=int, nargs=2, metavar=("W", "H"), default=(100, 50),
                        help="Set the cell size.")

    parser.add_argument("--no_prefetch", action="store_true",
                        help="Don't a separate thread to pre-fetch images.")

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
    f = MainFrame(None, imgpaths, args.rows_page, args.lookahead, args.num_cols, args.cellsize, args.no_prefetch)
    f.Show()
    app.MainLoop()

if __name__ == '__main__':
    main()
