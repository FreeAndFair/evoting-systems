import os, sys, math, csv, copy, pdb, traceback, time
import util_gui
from wx.lib.scrolledpanel import ScrolledPanel

"""
Contains two main widgets:
    ImageViewer(wx.ScrolledWindow)
    BallotScreen(ImageViewer)
"""

####
## Import 3rd party libraries
####

try:
    import wx
    import wx.animate
except ImportError:
    print """Error importing wxPython (wx) -- to install wxPython (a Python GUI \
library), do (if you're on Linux):
    sudo apt-get install python-wxgtk2.8
Or go to: 
    http://www.wxpython.org/download.php
For OS-specific installation instructions."""
    exit(1)
try:
    import Image
except ImportError:
    print """Error importing Python Imaging Library (Image) -- to install \
PIL (a Python image-processing library), go to: 
    http://www.pythonware.com/products/pil/"""
    exit(1)
try:
    import cv2
except ImportError:
    print """Error importing OpenCV w/ Python bindings (cv2) -- to install \
OpenCV w/ Python bindings (a Python computer vision library), go to:
    http://opencv.willowgarage.com/wiki/
Note that documentation for installing OpenCV is pretty shaky in my \
experience. A README section on installing OpenCV will be created soon.
On Windows, to get the Python bindings, copy/paste the contents of:
    opencv/build/python/2.7 (or 2.6)
to the site-packages directory of your Python installation, i.e.:
    C:/Python27/Lib/site-packages/
For me, this means that you'll be adding two new files to that directory:
    C:/Python27/Lib/site-packages/cv.py
    C:/Python27/Lib/site-packages/cv2.pyd"""
    exit(1)
try:
    import numpy as np
except ImportError:
    print """Error importing Numpy (numpy) -- to install Numpy, go to:
    http://numpy.scipy.org/
You'll probably want to install both scipy and numpy."""
    exit(1)
import wx.lib.inspection
from wx.lib.pubsub import Publisher

# Get this script's directory. Necessary to know this information
# since the current working directory may not be the same as where
# this script lives (which is important for loading resources like
# imgs)
try:
    MYDIR = os.path.abspath(os.path.dirname(__file__))
except NameError:
    # This script is being run directly
    MYDIR = os.path.abspath(sys.path[0])

"""
ImageViewer is a basic widget that is used to allow an image to be 
read in, and allow zooming in/out, drawing boxes, importing/exporting 
box locations.
You can subclass it to modify behavior (as I will do for BallotScreen), 
but this widget's default behavior is:
    
    - View an image
    - Draw bounding boxes
    - Import/export bounding box locations
    - Zoom in/out
    
To modify this behavior, you'll definitely want to modify the mouse-event
handlers (onLeftDown, onLeftUp, onMotion, etc.) to get exactly the
behavior you'd like.
"""

class ImageViewer(wx.ScrolledWindow):
    """
    Window that displays an image, and lets the draw boxes.
    """
    
    """
    STATE_IDLE: User can create boxes (by clicking+dragging), and
                resize boxes (dragging LR corner)
    STATE_ZOOM_IN: User left-clicks to zoom-in, right-clicks to zoom
                   out
    STATE_ZOOM_OUT: User left-clicks to zoom-out, right-clicks to zoom
                    int
    
    STATE_RESIZE_TARGET: Activated when the user's mouse is near the
                         LR corner of a box, but not during ZOOM_IN/OUT
    """
    
    # Constants used for Edit State
    STATE_IDLE = 0
    STATE_ZOOM_IN = 5
    STATE_ZOOM_OUT = 6
    
    # Aux States
    STATE_RESIZE_TARGET = 6
    
    def __init__(self, parent, world,
                 can_resize=True, 
                 can_delete=True,
                 can_modify=True,
                 *args, **kwargs):
        """
        obj world: An object storing all shared state between widgets.
                   Should be of type WorldState
        """
        wx.ScrolledWindow.__init__(self, parent, *args, **kwargs)
        self.parent = parent
        # Instance vars
        self.world = world
        self.scale = 1.0    # What current scale level we're at
        self.curstate = ImageViewer.STATE_IDLE
        self.auxstate = None  # i.e. being in 'modify' and 'resize' state at once

        # behavior flags
        self._is_resize_enabled = can_resize
        self._is_delete_enabled = can_delete
        self._is_modify_enabled = can_modify

        self.target_width = 40
        self.target_height = 30

        self.current_imgpath = None # Currently-displayed imgpath
        self.img_pil = None         # Original PIL image (no resizing)
        self.img_resize_pil = None  # PIL image that was resized
        self.img_bitmap = None      # wxBitmap object used (for painting)
        
        self._grabbed_box = None  # Currently 'grabbed' target (if any)
                                  # Note: Only used by ImageViewer atm
        self._new_box = None      # Member to be used to temporarily store
                                  # a box being created for the first time
        self._sel_boxes = []    # Currently selected boxes
        self._resize_target = None # Current target that's being resized (if any)
        self._resize_mode = ''    # One of 'top', 'bottom', 'left', 'right', 'upperleft', ...
        self._resize_rect = None    # (Client) coords of target being resized:
                                    # (<upper-left x>, <u-l y>, <lower-right x>, <l-r y>)
        self._prev_cursor = None    # Store the previous cursor
        self._prev_state = None
        self._prev_auxstate = None
        
        self._dragselectregion = []  # (Client) coords of a click-and-drag 
                                       # selection box made by the user

        self._resize_cursor_flag = False   # Used for changing mouse cursor for resizing targets
        self._delete_cursor_flag = False    # Used for changing mouse cursor for deleting boxes
        self._can_drag = False              # Used to allow better click-drag behavior
        
        self._oldmousepos = None    # Used to keep track of last mouse position
                                    # for dragging boxes around
                                  
        self.state_stack = []       # A stack of WorldState objects.
                                    # Used to enable undo, etc.
        # Pubsub callbacks
        self.callbacks = [("broadcast.push_state", self._pubsub_push_state),
                          ("broadcast.updated_world", self._pubsub_updated_world),
                          ("signals.BallotScreen.zoom", self._pubsub_zoom)]

        # Initialization
        self.subscribe_pubsubs()
        self._init_ui()
        self._bind_events()
        
    def subscribe_pubsubs(self):
        for (topic, callback) in self.callbacks:
            Publisher().subscribe(callback, topic)

    def unsubscribe_pubsubs(self):
        for (topic, callback) in self.callbacks:
            Publisher().unsubscribe(callback, topic)

    def _init_ui(self):
        # Grab default image
        self.set_image(None)
        
    def is_resize_enabled(self):
        return self._is_resize_enabled
    def is_delete_enabled(self):
        return self._is_delete_enabled
    def is_modify_enabled(self):
        return self._is_modify_enabled

    def _bind_events(self):
        for evt, handler in [
                (wx.EVT_LEFT_DOWN, self.onLeftDown),    # Create/Lift voting target box
                (wx.EVT_LEFT_UP, self.onLeftUp),        # Drop voting target box
                (wx.EVT_RIGHT_DOWN, self.onRightDown),  # Modify voting target box
                (wx.EVT_MOTION, self.onMotion),         # Move/Resize voting target box        
                (wx.EVT_SIZE, self.onSize),             # Signal to redraw screen (not sure if needed)
                (wx.EVT_IDLE, self.onIdle),             # Redraw
                (wx.EVT_PAINT, self.onPaint),           # Refresh
                (wx.EVT_ERASE_BACKGROUND, self.onEraseBackground),
                (wx.EVT_WINDOW_DESTROY, self.cleanup)]:
            self.Bind(evt, handler)
        
    def set_image(self, imgpath):
        """
        Displays the given image. If None is passed, then displays an
        empty bitmap instead.
        """
        self.reset_scale()
        # Reset state
        self.current_imgpath = imgpath
        self.unselect_boxes()
        if not imgpath:
            ones = np.ones((500, 500))
            ones *= 200
            img = Image.fromarray(ones)
        else:
            img = util_gui.open_as_grayscale(imgpath)
        self.img_pil = img
        w_client = self.GetClientSize()[0]
        _factor = img.size[0] / float(w_client)
        new_h = int(round(img.size[1] / _factor))
        img_rescale = img.resize((w_client, new_h), Image.ANTIALIAS)
        self.img_resize_pil = img_rescale
        imgbitmap = util_gui.PilImageToWxBitmap(img_rescale)
        # bitmap upper left corner is in the position tuple (x, y) = (5, 5)
        self.img_bitmap = imgbitmap
        #self.set_state(ImageViewer.STATE_IDLE)
        self._setup_scrollbars()
        
    def set_image_pil(self, imgpath, img_pil):
        def compute_scale(imgsize, w_client):
            """
            Return the scale that most closely ensures that the
            img width matches the client width.
            """
            w_img,h_img = imgsize
            _factor = float(w_client) / w_img
            return _factor
        self.current_imgpath = imgpath
        self.img_pil = img_pil
        # Scale img s.t. its height matches this Client width
        self.reset_scale()
        # Reset state
        if self.get_selected_boxes():
            for box in self.get_selected_boxes():
                self.unselect_target(box)
            
        w_img, h_img = img_pil.size
        w_client = self.GetClientSize()[0]
        new_scale = compute_scale((w_img, h_img), w_client)
        self.set_scale(new_scale)
        self.Refresh()
        
    def _setup_scrollbars(self):
        ## Scrollbar calculations
        _num_scrolls_x, _num_scrolls_y = 10.0, 10.0
        w_client, h_client = self.GetClientSize()
        w_img, h_img = (max(self.img_bitmap.GetWidth(), w_client),
                        max(self.img_bitmap.GetHeight(), h_client))
        x, y = round(w_img / _num_scrolls_x), round(h_img / _num_scrolls_y)
        self.SetScrollbars(x, y, _num_scrolls_x, _num_scrolls_y, noRefresh=True)
        
    def get_imgsize(self):
        """
        Return the native (unscaled) size of the displayed image.
        """
        return self.img_pil.size

    def get_bitmapsize(self):
        """
        Return the size of the current bitmap being displayed to the
        user (which could be smaller/larger than self.get_imgsize)
        """
        return self.img_bitmap.GetWidth(), self.img_bitmap.GetHeight()

    def get_boxes(self):
        return self.world.get_boxes(self.current_imgpath)
    def get_targets(self):
        return [t for t in self.get_boxes() if not t.is_contest]
    def get_contests(self):
        return [c for c in self.get_boxes() if c.is_contest]
    def remove_box(self, b):
        self.world.remove_box(self.current_imgpath, b)
    def add_box(self, b):
        self.world.add_box(self.current_imgpath, b)
    def add_boxes(self, boxes):
        self.world.add_boxes(self.current_imgpath, boxes)

    def reset_scale(self):
        """ Called when, say, loading a new image """
        self.scale = 1.0
        
    def scale_image(self):
        """ Rescales image (keep aspect ratio) to fill in available space """
        w_client, h_client = self.GetClientSize()
        w_img, h_img = self.get_imgsize()
        factor = float(w_client) / w_img
        self.set_scale(factor)
        
    def set_scale(self, scale):
        """
        Changes the scale of the entire ImageViewer (used for zooming
        in/out.
        Input:
            float scale -- a float >0.0, where 1.0 represents 'normal scale'
        """
        def dofancyresize(imgsize, scale):
            if scale < 1.0:
                return True
            else:
                return False
        if scale <= 0.1:
            # Set limit on zooming-out
            return

        self.scale = scale
        # Rescale img bitmap
        w, h = self.img_pil.size
        w_scaled, h_scaled = int(round(w*scale)), int(round(h*scale))
        if dofancyresize((w,h), scale):
            rescaled_img = self.img_pil.resize((w_scaled, h_scaled), resample=Image.ANTIALIAS)
        else:
            rescaled_img = self.img_pil.resize((w_scaled, h_scaled))
        self.img_resize_pil = rescaled_img
        self.img_bitmap = util_gui.PilImageToWxBitmap(rescaled_img)
        self._setup_scrollbars()
        
    def increase_scale(self, amt):
        self.set_scale(self.scale + amt)
    def decrease_scale(self, amt):
        self.set_scale(self.scale - amt)
        
    def to_scaled_coords(self, (x,y)):
        """ Convert (x,y) client coords to scaled-client coords """
        return int(round(x*self.scale)), int(round(y*self.scale))
        
    def set_state(self, newstate):
        if newstate not in (ImageViewer.STATE_IDLE, 
                         ImageViewer.STATE_ZOOM_IN,
                         ImageViewer.STATE_ZOOM_OUT,
                         ImageViewer.STATE_RESIZE_TARGET):
            print "Incorrect newstate provided:", newstate
            return
        oldstate = self.curstate
        self.curstate = newstate
        
        self.set_cursor(newstate)
        self.Refresh()
        
    def set_auxstate(self, newstate):
        self.auxstate = newstate
        self.set_cursor(newstate)
        
    def pop_state(self):
        if self.state_stack:
            if len(self.state_stack) == 1:
                # Always maintain the 'first' worldstate
                return self.state_stack[0].copy()
            else:
                return self.state_stack.pop()
        else:
            return None
    def push_state(self, worldstate):  
        """
        For convenience, this function will make a copy of 'worldstate',
        instead of relying on the caller to copy the worldstate.
        """
        self.state_stack.append(worldstate.copy())
    def undo(self):
        """
        Reverts the current WorldState to a prior one.
        """
        oldstate = self.pop_state()
        if oldstate:
            self.world.mutate(oldstate)
            Publisher().sendMessage("broadcast.updated_world")
            
    def set_cursor(self, state):
        if state == ImageViewer.STATE_ZOOM_IN or state == ImageViewer.STATE_ZOOM_OUT:
            c = wx.CURSOR_MAGNIFIER
        elif state == ImageViewer.STATE_RESIZE_TARGET:
            c = wx.CURSOR_SIZENWSE
        else:
            c = wx.CURSOR_ARROW
        self.SetCursor(wx.StockCursor(c))
        
    def set_target_width(self, w):
        self.target_width = w
        
    def set_target_height(self, h):
        self.target_height = h
        
    def import_locations(self, csvfilepath):
        """ 
        Import locations (both targets and contests) from 'csvfilepath'.
        OUTDATED: Doesn't use self.world yet.
        """
        fields = ('imgpath', 'id', 'x', 'y', 'width', 'height', 'label', 'is_contest', 'contest_id')
        try:
            csvfile = open(csvfilepath, 'rb')
            dictreader = csv.DictReader(csvfile)
            w_img, h_img = self.img_pil.size
            # Ensure that target ID's are consecutive
            sorted_rows = sorted([row for row in dictreader], key=lambda r: int(r['id']))
            for i, row in enumerate(sorted_rows):
                # Scaling that has to be done
                x1 = float(row['x']) / float(w_img)
                y1 = float(row['y']) / float(h_img)
                x2 = x1 + (float(row['width']) / float(w_img))
                y2 = y1 + (float(row['height']) / float(h_img))
                is_contest = True if int(row['is_contest']) == 1 else False
                contest_id = int(row['contest_id'])
                target = BoundingBox(x1, y1, x2, y2,
                                     label=row['label'],
                                     is_contest=is_contest,
                                     contest_id=contest_id,
                                     id=i)
                assert target.contest_id == contest_id
                self.world.add_box(os.path.abspath(self.current_imgpath), target)
                assert target.contest_id == contest_id
            self.Refresh()
        except IOError as e:
            print "Unable to open file: {0}".format(csvfilepath)        
        
    def export_locations(self, outfilepath):
        """ Save all bounding boxes (targets, contests) to CSV file """
        fields = ['imgpath', 'id', 'x', 'y', 'width', 'height', 'label', 'is_contest', 'contest_id']
        try:
            csvfile = open(outfilepath, 'wb')
            dictwriter = csv.DictWriter(csvfile, fieldnames=fields)
            try:
                dictwriter.writeheader()
            except AttributeError:
                util_gui._dictwriter_writeheader(csvfile, fields)
            bounding_boxes = self.world.get_boxes(self.current_imgpath)
            if self.get_selected_boxes():
                bounding_boxes.extend(self.get_selected_boxes())
            # Let's avoid holes in ID's, which may cause headaches down the line
            bounding_boxes = sorted(bounding_boxes, key=lambda t: t.id)
            # Ensure that ID's are consecutive via use of 'enumerate'
            for id, t in enumerate(bounding_boxes):
                t.id = id
                row = {}
                row['imgpath'] = os.path.abspath(self.current_imgpath)
                row['id'] = id
                # Unscaling that has to be done
                w_img, h_img = self.img_pil.size
                row['x'] = int(round(t.x1 * w_img))
                row['y'] = int(round(t.y1 * h_img))
                width = int(round(abs(t.x1 - t.x2) * w_img))
                height = int(round(abs(t.y1 - t.y2) * h_img))
                row['width'] = width
                row['height'] = height
                # Replace commas with underscore to avoid problems with csv files
                row['label'] = t.label.replace(",", "_")
                row['is_contest'] = 1 if t.is_contest else 0
                row['contest_id'] = t.contest_id
                dictwriter.writerow(row)
            csvfile.close()
        except IOError as e:
            print "Couldn't write to file:", outfilepath            
        
    #### PubSub callbacks
        
    def _update_state(self, msg):
        self.set_state(msg.data)
    def _new_image(self, msg):
        """
        Happens when the user loads up a new image, File->Open...
        """
        filepath = msg.data
        self.set_image(filepath)
        self.set_state(ImageViewer.STATE_IDLE)
        self.Refresh()
    def _pubsub_push_state(self, msg):
        """
        Triggered whenever the world gets modified by the user (in a
        way that we want to be undo'd.
        """
        worldstate = msg.data
        self.push_state(worldstate)
    def _pubsub_updated_world(self, msg):
        """
        Triggered whenever the world changes. Check to see if any of
        the boxes are selected. Updates my internal data structs, but
        don't modify the world itself.
        """
        #self.unselect_boxes()
        self._sel_boxes = []
        for box in self.world.get_boxes(self.current_imgpath):
            if box.is_selected:
                self.select_target(box)
        self.Refresh()

    def _pubsub_zoom(self, msg):
        """
        Triggered when the user clicks the 'Zoom In/Out' button on the
        ToolBar.
        """
        type = msg.data
        if type == 'in':
            amt = 1.2
        else:
            amt = 0.8
        self.zoom_and_center(amt)

    def zoom_and_center(self, amt):
        """
        Zoom in/out by amt, and also center the viewport.
        If amt > 1.0, then zoom in. Otherwise zoom out.
        """
        x,y = self.GetClientSize()[0] / 2, self.GetClientSize()[1] / 2
        x,y = self.CalcUnscrolledPosition((x,y))
        old_scale = self.scale
        # If the image gets too small, an EVT_SIZE event is fired, which
        # expands image to max-fit -- annoying when zooming out a lot.
        self.Unbind(wx.EVT_SIZE)
        if amt >= 1.0:
            self.increase_scale(amt - 1.0)
        else:
            self.decrease_scale(1.0 - amt)

        new_virt_pos = (x*(self.scale / old_scale), y*(self.scale / old_scale))
        self.center_viewport(new_virt_pos, (x,y))
        self.Refresh()
        self.Bind(wx.EVT_SIZE, self.onSize)
        
    def get_closest_target(self, mousepos, boxes=None, mode="upper-left"):
        """
        Given current mouse position, return the closest target w.r.t 
        to the current 'mode'. Works both for voting targets and contests.
        Modes:
            mode="upper-left"
            mode="upper-right"
            mode="lower-right"
            mode="bounding-box"
        If boxes isn't given, then use self.boxes, etc.
        """
        if not boxes:
            boxes = self.world.get_boxes(self.current_imgpath)
            if self._grabbed_box:
                boxes += [self._grabbed_box]
        w_img, h_img = self.img_bitmap.GetWidth(), self.img_bitmap.GetHeight()
        if mode == "upper-left":
            candidates = sorted([t for t in boxes if util_gui.is_close_to(mousepos, (t.x1*w_img, t.y1*h_img))],
                                key=lambda t : util_gui.dist_euclidean(mousepos, (t.x1*w_img, t.y1*h_img)))
            return candidates[0] if candidates else None
        elif mode == "lower-right":
            candidates = sorted([t for t in boxes if util_gui.is_close_to(mousepos, ((t.x1+t.width)*w_img, (t.y1+t.height)*h_img))],
                                key=lambda t: util_gui.dist_euclidean(mousepos, ((t.x1+t.width)*w_img, (t.y1+t.height)*h_img)))
            return candidates[0] if candidates else None
        elif mode == "upper-right":
            candidates = sorted([t for t in boxes if util_gui.is_close_to(mousepos, ((t.x1+t.width)*w_img, t.y1*h_img))],
                                key=lambda t: util_gui.dist_euclidean(mousepos, ((t.x1+t.width)*w_img, t.y1*h_img)))
            return candidates[0] if candidates else None
        elif mode == "lower-left":
            candidates = sorted([t for t in boxes if util_gui.is_close_to(mousepos, ((t.x1)*w_img, (t.y1+t.height)*h_img))],
                                key=lambda t: util_gui.dist_euclidean(mousepos, ((t.x1)*w_img, (t.y1+t.height)*h_img)))
            return candidates[0] if candidates else None            
        elif mode == 'top':
            candidates = sorted([t for t in boxes if util_gui.is_close_to(mousepos, ((t.x1+(t.width/2.0))*w_img, t.y1*h_img))],
                                key=lambda t: util_gui.dist_euclidean(mousepos, ((t.x1+(t.width/2.0))*w_img, t.y1*h_img)))
            return candidates[0] if candidates else None
        elif mode == 'bottom':
            candidates = sorted([t for t in boxes if util_gui.is_close_to(mousepos, ((t.x1+(t.width/2.0))*w_img, (t.y1+t.height)*h_img))],
                                key=lambda t: util_gui.dist_euclidean(mousepos, ((t.x1+(t.width/2.0))*w_img, (t.y1+t.height)*h_img)))
            return candidates[0] if candidates else None
        elif mode == 'left':
            candidates = sorted([t for t in boxes if util_gui.is_close_to(mousepos, (t.x1*w_img, (t.y1+t.height/2.0)*h_img))],
                                key=lambda t : util_gui.dist_euclidean(mousepos, (t.x1*w_img, (t.y1+t.height/2.0)*h_img)))
            return candidates[0] if candidates else None
        elif mode == 'right':
            candidates = sorted([t for t in boxes if util_gui.is_close_to(mousepos, ((t.x1+t.width)*w_img, (t.y1+(t.height/2.0))*h_img))],
                                key=lambda t: util_gui.dist_euclidean(mousepos, ((t.x1+t.width)*w_img, (t.y1+(t.height/2.0))*h_img/2)))
            return candidates[0] if candidates else None
        elif mode == "bounding-box":
            x, y = mousepos
            candidates = []
            for box in boxes:
                x_t, y_t = int(round(box.x1 * w_img)), int(round(box.y1 * h_img))
                w_t, h_t = int(round(box.width * w_img)), int(round(box.height * h_img))
                if util_gui.is_on_bounding_box(mousepos, (x_t, y_t), w_t, h_t, 3):
                    candidates.append(box)
            return candidates[0] if candidates else None
        elif mode == "interior":
            x, y = mousepos
            candidates = []
            for box in boxes:
                x1_box, y1_box = int(round(box.x1 * w_img)), int(round(box.y1 * h_img))
                w_box, h_box = int(round(box.width * w_img)), int(round(box.height * h_img))
                if (x >= x1_box and x <= (x1_box+w_box)
                        and y >= y1_box and y <= (y1_box+h_box)):
                    candidates.append(box)
            # To handle case where there are nested boxes, we want the
            # 'inner-most' box to be returned, which I believe will
            # always be the closest box w.r.t upper-left corner.
            fn = util_gui.dist_euclidean
            if not candidates:
                return None
            return sorted(candidates, 
                          key=lambda box: fn(mousepos,
                                             (box.x1*w_img, box.y1*h_img)))[0]
        else:
            raise RuntimeException("Error: in BallotScreen.get_closest_target(3), \
unexpected mode given: {0}".format(mode))
                
    def get_closest_resize_box(self, targets, mousepos):
        """
        Like get_closest_target(5), but only to get candidate boxes
        for resizing purposes.
        Output:
            obj boundingbox, str mode
        """
        modes = ['upper-left', 'upper-right', 'lower-left', 'lower-right',
                 'top', 'bottom', 'left', 'right']
        for mode in modes:
            t = self.get_closest_target(mousepos, boxes=targets, mode=mode)
            if t:
                return t, mode
        return None, ''
    def get_closest_box_any(self, targets, mousepos):
        """
        Like get_closest_target(5), but also returns the mode.
        Output:
            obj boundingbox, str mode
        """
        modes = ['upper-left', 'upper-right', 'lower-left', 'lower-right',
                 'top', 'bottom', 'left', 'right', 'interior']
        for mode in modes:
            t = self.get_closest_target(mousepos, boxes=targets, mode=mode)
            if t:
                return t, mode
        return None, ''                 

    def get_selected_boxes(self):
        return self._sel_boxes
            
    def select_target(self, box):
        if box not in self._sel_boxes:
            box.select()
            self._sel_boxes.append(box)
            
    def unselect_boxes(self):
        """ Unselect all currently-selected boxes """
        for box in self._sel_boxes:
            box.unselect()
        self._sel_boxes = []

    def unselect_target(self, box):
        """ Unselect the currently selected target """
        box.unselect()
        self._sel_boxes.remove(box)
        
    def is_select_target(self):
        """
        Returns True if a target is selected at the moment.
        """
        return self._sel_boxes
    
    def enable_dragging(self):
        """
        Allows the user to click-drag a selected BoundingBox. 
        """
        self._can_drag = True
    def disable_dragging(self):
        self._can_drag = False
    def can_drag(self):
        """
        Returns True iff the user is allowed to click-drag a Box.
        """
        return self._can_drag
    
    def is_new_box(self):
        """
        Returns True if a box is in the middle of being created.
        """
        return self._new_box != None
    def set_new_box(self, b):
        """
        Registers 'b' as being a box currently being created (i.e.
        the user left-clicked down, and currently is deciding the
        dimensions of the box, but hasn't yet released the left-mouse
        btn.
        """
        assert self._new_box == None
        self._new_box = b
        self._new_box.is_new = True
    def unset_new_box(self):
        assert self._new_box != None
        self._new_box.is_new = False
        self._new_box = None
        
    def get_new_box(self):
        return self._new_box
    
    def set_resize_target(self, box, corner):
        """ 
        Select a box for it to be resized by the user.
        Input:
            obj box: A BoundingBox instance that is being resized
            str mode: One of 'top', 'bottom', 'left', 'right', 
                        'upperleft', 'upperright', 'lowerleft', or
                        'lowerright', to signify how to resize box.
        """
        self._resize_target = box
        self._resize_mode = corner
        w_img, h_img = self.img_bitmap.GetWidth(), self.img_bitmap.GetHeight()
        x1, y1 = int(round(box.x1 * w_img)), int(round(box.y1 * h_img))
        x2 = int(round(box.x1*w_img + box.width*w_img))
        y2 = int(round(box.y1*h_img + box.height*h_img))
        self._resize_rect = [x1, y1, x2, y2]
        
    def unset_resize_target(self):
        self._resize_target = None
        self._resize_rect = None
        self._resize_mode = ''
        
    def is_resize_target(self):
        """ Return True if a user is currently resizing a target """
        return self._resize_target != None
        
    def delete_target(self, box):
        if box in self.world.get_boxes(self.current_imgpath):
            self.world.remove_box(self.current_imgpath, box)
        else:
            print "ImageViewer.delete_target: BoundingBox wasn't found:", box            
        if box in self.get_selected_boxes()[:]:
            self.unselect_target(box)

    def center_viewport(self, virt_pos, client_pos):
        """ 
        Centers view onto mousepos, by adjusting the scrollbars. 
        mousepos is a tuple (x,y) that is in client coordinates.
        """
        if self.GetScrollPixelsPerUnit()[0]:
            _round = lambda x: int(round(x))
            x,y = virt_pos
            x_offset = _round((self.GetClientSize()[0])/2.0)
            y_offset = _round((self.GetClientSize()[1])/2.0)
            x_foo = x-x_offset if x-x_offset > 0 else 0
            y_foo = y-y_offset if y-y_offset > 0 else 0
            x_scrollunit = _round(x_foo / float(self.GetScrollPixelsPerUnit()[0]))
            y_scrollunit = _round(y_foo / float(self.GetScrollPixelsPerUnit()[1]))
            self.Scroll(x_scrollunit, y_scrollunit)
        
    #### Event handlers
    
    def onLeftDown(self, event):
        """
        Depending on the edit mode, either creates a new voting target
        box, or moves an existing voting target box (if the mouse is
        close to one).
        """
        x, y = self.CalcUnscrolledPosition(event.GetPositionTuple())
        if (self.curstate == ImageViewer.STATE_IDLE
                and not self._resize_cursor_flag):
            # Create new box at mouse location
            w_img, h_img = self.img_bitmap.GetWidth(), self.img_bitmap.GetHeight()
            x1_rel, y1_rel = x / float(w_img), y / float(h_img)
            x2_rel, y2_rel = (x+1)/float(w_img), (y+1)/float(h_img) #x1_rel, y1_rel
            new_box = BoundingBox(x1_rel, y1_rel, x2_rel, y2_rel)
            self._grabbed_box = new_box
            self.Refresh()
            return
        elif self.curstate == ImageViewer.STATE_ZOOM_IN:
            old_virt_pos = (x,y)
            old_scale = self.scale
            self.increase_scale(0.2)
            new_virt_pos = (x*(self.scale / old_scale), y*(self.scale / old_scale))
            self.center_viewport(new_virt_pos, event.GetPositionTuple())
            self.Refresh()
        elif self.curstate == ImageViewer.STATE_ZOOM_OUT:
            old_virt_pos = (x,y)
            old_scale = self.scale
            self.decrease_scale(0.2)
            new_virt_pos = (x*(self.scale / old_scale), y*(self.scale / old_scale))
            self.center_viewport(new_virt_pos, event.GetPositionTuple())
            self.Refresh()
            
        if (self.curstate == ImageViewer.STATE_IDLE):
            t, mode = self.get_closest_resize_box(self.world.get_boxes(self.current_imgpath), (x,y))
            if t and self.is_resize_enabled():
                self.set_resize_target(t, mode)
                self._prev_auxstate = self.auxstate
                self.set_auxstate(ImageViewer.STATE_RESIZE_TARGET)
                self.Refresh()
        event.Skip()
        
    def onLeftUp(self, event):
        """ Drop the voting target box at the current mouse location. """
        mousepos = self.CalcUnscrolledPosition(event.GetPositionTuple())
        if (self.curstate == ImageViewer.STATE_IDLE
                and self._grabbed_box):
            self.push_state(self.world)
            self.world.add_box(self.current_imgpath, self._grabbed_box)
            self._grabbed_box.set_color("Green")
            self._grabbed_box = None
            self.Refresh()
            return
        
        # Auxillary State Handling
        if self.auxstate == ImageViewer.STATE_RESIZE_TARGET:
            if self.is_resize_target():
                x, y = mousepos
                x1, y1, x2, y2 = self._resize_rect
                (ul_x, ul_y), (lr_x, lr_y) = util_gui.get_box_corners((x1, y1), (x2, y2))
                w_pixs = int(round((abs(x2-x1) / float(self.img_bitmap.GetWidth())) * self.img_pil.size[0]))
                h_pixs = int(round((abs(y2-y1) / float(self.img_bitmap.GetHeight())) * self.img_pil.size[1]))
                self._resize_target.x1 = ul_x / float(self.img_bitmap.GetWidth())
                self._resize_target.y1 = ul_y / float(self.img_bitmap.GetHeight())
                self._resize_target.x2 = lr_x / float(self.img_bitmap.GetWidth())
                self._resize_target.y2 = lr_y / float(self.img_bitmap.GetHeight())
                self.unset_resize_target()
                self.set_auxstate(self._prev_auxstate)
                self._prev_auxstate = None
                
        self.Refresh()
        event.Skip()
        
    def onRightDown(self, event):
        """
        If the edit mode is 'Modify', then if the user right-clicks a
        voting target box, bring up a selection to modify it (say,
        dimensions of that particular box.
        Not sure if needed.
        """
        x,y = self.CalcUnscrolledPosition(event.GetPositionTuple())        
        if (self.curstate == ImageViewer.STATE_ZOOM_IN):
            old_virt_pos = (x,y)
            old_scale = self.scale
            
            self.decrease_scale(0.2)

            new_virt_pos = (x*(self.scale / old_scale), y*(self.scale / old_scale))
            
            self.center_viewport(new_virt_pos, event.GetPositionTuple())
            self.Refresh()
        elif self.curstate == ImageViewer.STATE_ZOOM_OUT:
            old_virt_pos = (x,y)
            old_scale = self.scale
            
            self.increase_scale(0.2)

            new_virt_pos = (x*(self.scale / old_scale), y*(self.scale / old_scale))
            
            self.center_viewport(new_virt_pos, event.GetPositionTuple())
            self.Refresh()
        self.Refresh()
        event.Skip()
        
    def onMotion(self, event):
        """
        Depending on the edit mode, move the voting target box 
        currently held by the user.
        """
        x, y = self.CalcUnscrolledPosition(event.GetPositionTuple())
        if (self.curstate == ImageViewer.STATE_IDLE
                and self.get_closest_target((x,y), mode="lower-right")
                and not self.is_resize_target()
                and not self._resize_cursor_flag):
            # We just entered LR corner of a voting box
            myCursor= wx.StockCursor(wx.CURSOR_SIZENWSE)
            self._prev_cursor = self.GetCursor()
            self.SetCursor(myCursor)
            self._resize_cursor_flag = True
            self.Refresh()
        elif (self.curstate == ImageViewer.STATE_IDLE
                and not self.get_closest_target((x,y), mode="lower-right")
                and not self.is_resize_target()
                and self._resize_cursor_flag):
            # Mouse just left region of LR corner of a voting box
            self.SetCursor(self._prev_cursor)
            self._prev_cursor = None
            self._resize_cursor_flag = False
            self.Refresh()
        elif (self._grabbed_box 
                and self.curstate == ImageViewer.STATE_IDLE
                and event.LeftIsDown()
                and not self._resize_cursor_flag):
            w_img, h_img = self.img_bitmap.GetWidth(), self.img_bitmap.GetHeight()
            x_rel, y_rel = x / float(w_img), y / float(h_img)
            self._grabbed_box.x2 = x_rel
            self._grabbed_box.y2 = y_rel
            self._grabbed_box.set_color("Red")
            self.Refresh()            
        elif self.get_selected_boxes() and event.LeftIsDown():
            w_img, h_img = self.img_bitmap.GetWidth(), self.img_bitmap.GetHeight()
            for box in self.get_selected_boxes():
                box.x2 = x / float(w_img)
                box.y2 = y / float(h_img)
                box.set_color("Red")
            self.Refresh()        
        # Aux State Handling
        if (self.auxstate == ImageViewer.STATE_RESIZE_TARGET
                and self.is_resize_target()):
            self._resize_rect = [self._resize_rect[0], self._resize_rect[1],
                                 x, y]
            self.Refresh()
        event.Skip()
        
    def onSize(self, event):
        """ Rescale image to fill available space (maintain aspect ratio) """
        if self.img_bitmap:
            width_client, height_client = self.GetClientSize()
            width_img, height_img = self.img_bitmap.GetSize()
            if abs(width_client - width_img) >= 40:
                self.scale_image()
        self.Refresh()
        event.Skip()

    def onIdle(self, event):
        """ Redraw screen. """
        self.Update()
        event.Skip()
        
    def onPaint(self, event):
        """ Refresh screen. """
        if self.IsDoubleBuffered():
            dc = wx.PaintDC(self)
        else:
            dc = wx.BufferedPaintDC(self)
        # You must do PrepareDC in order to force the dc to account
        # for scrolling.
        self.PrepareDC(dc)
        dc.DrawBitmap(self.img_bitmap, 0, 0)
        self._display_targets(dc)
        if self.auxstate == ImageViewer.STATE_RESIZE_TARGET:
            self._draw_resize_rect(dc)
        if self._dragselectregion:
            self._draw_dragselectregion(dc)
        event.Skip()
        
    def _draw_dragselectregion(self, dc):
        """
        Draw the selection box created when a user click-drags
        in order to select multiple boxes.
        Assumes that self._dragselectregion is of the form:
            [upperleft_x, upperleft_y, lowerright_x, lowerright_y]
        """
        dc.SetBrush(wx.TRANSPARENT_BRUSH)
        dc.SetPen(wx.Pen("Black", 1.0))
        ul_x, ul_y, lr_x, lr_y = self._dragselectregion
        (ul_x, ul_y), (lr_x, lr_y) = util_gui.get_box_corners((ul_x,ul_y),
                                                              (lr_x, lr_y))
        w, h = abs(ul_x - lr_x), abs(ul_y - lr_y)
        dc.DrawRectangle(ul_x, ul_y, w, h)

    def _draw_box(self, dc, box):
        """
        Draws the input BoundingBox in DC dc. Correctly will 'correct'
        the x1,y1,x2,y2 coords of 'box' into canonical ul_x, ul_y,
        lr_x, lr_y (ul := Upper-Left, lr := Lower-Right).
        """
        CIRCLE_RAD = 1 if self.scale == 1.0 else 3
        dc.SetBrush(wx.TRANSPARENT_BRUSH)
        dc.SetPen(wx.Pen(box.color, box.line_width))
        
        w_img, h_img = self.img_bitmap.GetWidth(), self.img_bitmap.GetHeight()
        x1, y1 = int(round(box.x1*w_img)), int(round(box.y1*h_img))
        x2, y2 = int(round(box.x2*w_img)), int(round(box.y2*h_img))
        w, h = abs(x1-x2), abs(y1-y2)
        (ul_x, ul_y), (lr_x, lr_y) = util_gui.get_box_corners((x1,y1),(x2,y2))
        dc.DrawRectangle(ul_x,ul_y,w,h)
        # Draw the 'grabber' circles
        dc.SetPen(wx.Pen("Black", 1))
        dc.SetBrush(wx.Brush("White"))
        dc.DrawCircle(ul_x, ul_y, CIRCLE_RAD)           # Upper-Left
        dc.DrawCircle(ul_x+(w/2), ul_y, CIRCLE_RAD)     # Top
        dc.DrawCircle(ul_x+w, ul_y, CIRCLE_RAD)         # Upper-Right
        dc.DrawCircle(ul_x, ul_y+(h/2), CIRCLE_RAD)     # Left
        dc.DrawCircle(ul_x+w, ul_y+(h/2), CIRCLE_RAD)   # Right
        dc.DrawCircle(ul_x, ul_y+h, CIRCLE_RAD)         # Lower-Left
        dc.DrawCircle(ul_x+(w/2), lr_y, CIRCLE_RAD)     # Bottom
        dc.DrawCircle(lr_x, lr_y, CIRCLE_RAD)           # Lower-Right
        dc.SetBrush(wx.TRANSPARENT_BRUSH)
        
        # Draw the ID numbers (for now)
        #if box.is_contest:
        #    dc.SetTextForeground("Blue")
        #else:
        #    dc.SetTextForeground("Red")
        #dc.DrawText(str(box.contest_id), ul_x, ul_y)
        
    def _draw_resize_rect(self, dc):
        dc.SetBrush(wx.TRANSPARENT_BRUSH)
        dc.SetPen(wx.Pen("Orange", 3))
        x1, y1, x2, y2 = self._resize_rect
        (ul_x, ul_y), (lr_x, lr_y) = util_gui.get_box_corners((x1, y1), (x2, y2))
        w, h = abs(lr_x - ul_x), abs(lr_y - ul_y)
        dc.DrawRectangle(ul_x, ul_y, w, h)
        
    def _display_targets(self, dc):
        """ Only to be called from self.onPaint(2) """
        if self.current_imgpath:
            dc.SetBrush(wx.TRANSPARENT_BRUSH)
            for t in self.world.get_boxes(os.path.abspath(self.current_imgpath)):
                self._draw_box(dc, box)
        if self._grabbed_box:
            self._draw_box(dc, self._grabbed_box)
    def onEraseBackground(self, event):
        pass
        #event.Skip()
        
    def cleanup(self, event):
        """ Release held resources (like open image files). """
        event.Skip()
       
class WorldState(object):
    """
    A class to hold all shared state amongst widgets -- i.e. the
    'model', if you like Model-View-Controller parlance.
    Having each widget store its own 'copy' of the world is a
    BadIdea (tm).
    """
    def __init__(self, box_locations=None):
        if box_locations:
            self.box_locations = box_locations     # {str templatepath: list boxes}
        else:
            self.box_locations = {}
        self.callbacks = [("signals.world.set_boxes", self._pubsub_set_boxes),
                          ("broadcast.templatesdir", self._pubsub_templatesdir)]

    def subscribe_pubsubs(self):
        for (topic, callback) in self.callbacks:
            Publisher().subscribe(callback, topic)
    def unsubscribe_pubsubs(self):
        for (topic, callback) in self.callbacks:
            Publisher().unsubscribe(callback, topic)

    def get_boxes(self, imgpath):
        return self.box_locations.get(imgpath, [])
    def get_boxes_all(self):
        return self.box_locations
    def get_boxes_all_list(self):
        """
        Return a list of all BoundingBoxes as a flatlist. Useful if you want
        to perfrom some global operation on all boxes, like a global resize.
        """
        return reduce(lambda x,y: x+y, self.box_locations.values(), [])
    def get_boxes_count(self, imgpath):
        return len(self.get_boxes(imgpath))
    def get_boxes_count_all(self):
        return sum([self.get_boxes_count(path) for path in self.box_locations])

    def set_boxes(self, imgpath, boxes):
        self.box_locations[imgpath] = boxes

    def add_box(self, imgpath, box):
        if imgpath in self.box_locations and box in self.box_locations[imgpath]:
            print 'WorldState.add_box: {0} already in box_locations for {1}'.format(box, imgpath)
        else:
            self.box_locations.setdefault(imgpath, []).append(box)
    def add_boxes(self, imgpath, boxes):
        if not boxes:
            # Still register 'imgpath' into self.box_locations
            self.box_locations[imgpath] = []
        else:
            for b in boxes:
                self.add_box(imgpath, b)
    def remove_box(self, imgpath, box):
        self.box_locations[imgpath].remove(box)
    def remove_voting_targets(self, imgpath):
        self.box_locations[imgpath] = [b for b in self.box_locations[imgpath] if b.is_contest]
    def remove_contests(self, imgpath):
        self.box_locations[imgpath] = [b for b in self.box_locations[imgpath] if not b.is_contest]
       
    def mutate(self, worldstate):
        """
        Change this WorldState to match the input 'worldstate'. 
        Useful when you want to instantly change the world, i.e. for
        the Undo feature.
        """
        self.box_locations = worldstate.box_locations
    def reset(self):
        """
        Reset this WorldState to be 'blank'.
        """
        self.mutate(WorldState())

    def copy(self):
        newboxlocs = {}
        for tmppath, boxes in self.box_locations.iteritems():
            newboxlocs[tmppath] = [b.copy() for b  in boxes]
        return WorldState(newboxlocs)
        
    # Pubsub callbacks
    def _pubsub_templatesdir(self, msg):
        templatesdir = msg.data
        for dirpath, dirnames, filenames in os.walk(templatesdir):
            for imgname in [f for f in filenames if util_gui.is_image_ext(f)]:
                imgpath = os.path.abspath(os.path.join(dirpath, imgname))
                self.box_locations.setdefault(imgpath, [])
    def _pubsub_set_boxes(self, msg):
        self.box_locations = msg.data
       
class BoundingBox(object):
    """
    To account for image resizing, all coordinates (x1,y1,x2,y2)
    are floats from [0,1].
        (x1,y1) -- point 1, serves as the anchor.
        (x2,y2) -- point 2, can change w.r.t the mouse cursor.
    """
    ctr = 0
    ctr_contest = 0
    # Radius of the 'grab' circle in the upper-left corner
    CIRCLE_RAD = 5.5
    CIRCLE_COLOR = "Blue"
    
    def __init__(self, x1, y1, x2, y2, label='', color=None, 
                 id=None, is_contest=False, contest_id=None, 
                 target_id=None,
                 line_width=None, children=[],
                 is_new=False, is_selected=False):
        """
        bool is_contest: If True, then this is the bounding box for a
                         contest. O.w. this is a voting target.
        obj children: If present, then this BoundingBox is 'tied' to
                        other BoundingBoxes, such that if this 
                        BoundingBox gets deleted, then all of its
                        children should too.
        bool is_new: True iff this box is in the middle of being
                     created.
        bool is_selected: True iff this box is currently selected.
                        
        Note: id is subject to be changed if 'holes' in the id range
        are detected during importing/exporting voting targets.
        """
        self.x1, self.y1 = x1, y1
        self.x2, self.y2 = x2, y2
        self.label = label
        self.is_contest = is_contest
        self.is_new = is_new
        self.is_selected = is_selected
        if id != None:
            self.id = id
        else:
            self.id = BoundingBox.ctr
            BoundingBox.ctr += 1
        if contest_id != None:
            self.contest_id = contest_id
        else:
            self.contest_id = BoundingBox.ctr_contest
            BoundingBox.ctr_contest += 1
        self.target_id = target_id
        self.color = None
        if not color:
            self.restore_color()
        else:
            self.color = color
        self.line_width = None
        if not line_width:
            self.restore_line_width()
        else:
            self.line_width = line_width
        self.children = children

        
    def get_coords(self):
        """ Return x1,y1,x2,y2 as rel coords """
        return self.x1, self.y1, self.x2, self.y2
        
    @property
    def width(self):
        return abs(self.x1 - self.x2)
    @property
    def height(self):
        return abs(self.y1 - self.y2)
        
    def set_color(self, color):
        self.color = color
    def restore_color(self):
        """
        Depending on what kind of BoundingBox I am (voting target, or
        contest), set my color.
        """
        if self.is_contest:
            self.set_color("Blue")
        else:
            self.set_color("Orange")
    def restore_line_width(self):
        """
        Depending on what kind of BoundingBox I am (voting target, or
        contest), set the width of my line.
        """
        if self.is_contest:
            self.line_width = 3
        else:
            self.line_width = 2
    
    def select(self):
        self.set_color("Yellow")
        self.is_selected = True
    def unselect(self):
        self.restore_color()
        self.is_selected = False
        
    def copy(self):
        """ Return a copy of myself """
        return BoundingBox(self.x1, self.y1, 
                           self.x2, self.y2, label=self.label,
                           color=self.color, id=self.id, is_contest=self.is_contest,
                           contest_id=self.contest_id, is_new=self.is_new,
                           is_selected=self.is_selected,
                           target_id=self.target_id)

    def marshall(self):
        """
        Return a dict-equivalent of myself.
        """
        return {'x1': self.x1, 'y1': self.y1, 'x2': self.x2, 'y2': self.y2,
                'label': self.label, 'color': self.color, 'id': self.id,
                'is_contest': self.is_contest, 'contest_id': self.contest_id,
                'target_id': self.target_id, 'line_width': self.line_width,
                'children': self.children, 'is_new': self.is_new,
                'is_selected': self.is_selected}

    @staticmethod
    def unmarshall(data):
        """
        Returns a BoundingBox instance that is fed from 'data'.
        """
        box = BoundingBox(0,0,0,0)
        for (propname, propval) in data.iteritems():
            setattr(box, propname, propval)
        return box

    def __eq__(self, a):
        return (a and self.x1 == a.x1 and self.y1 == a.y1 and self.x2 == a.x2
                and self.y2 == a.y2 and self.is_contest == a.is_contest
                and self.label == a.label)
    def __repr__(self):
        return "BoundingBox({0},{1},{2},{3},label={4},is_contest={5})".format(self.x1, self.y1, self.x2, self.y2, self.label, self.is_contest)
    def __str___(self):
        return "BoundingBox({0},{1},{2},{3},label={4},is_contest={5})".format(self.x1, self.y1, self.x2, self.y2, self.label, self.is_contest)

class BallotViewer(wx.Panel):
    """
    Panel that contains a BallotScreen (displays an image, and allows
    creation of boxes), and a toolbar that controls the behavior of
    the BallotScreen.
    """
    def __init__(self, parent, world, ballotscreen=None, toolbar=None, *args, **kwargs):
        """
        obj parent: Parent widget.
        obj world: Object that stores all shared state between widgets
        obj ballotscreen: If given, then this should be a subclass of
                          BallotScreen.
        obj toolbar: If given, this should be a subclass of ToolBar.
        """
        wx.Panel.__init__(self, parent, *args, **kwargs)
        self.parent = parent
        self.world = world
        
        self.sizer = wx.BoxSizer(wx.VERTICAL)
        if not toolbar:
            self.toolbar = ToolBar(self)
        else:
            self.toolbar = toolbar(self)
        self.toolbar.disable_buttons()
        self.sizer.Add(self.toolbar, proportion=0, flag=wx.ALL | wx.ALIGN_LEFT)
        if not ballotscreen:
            self.ballotscreen = BallotScreen(self, self.world)
        else:
            self.ballotscreen = ballotscreen(self, self.world)
        self.sizer.Add(self.ballotscreen, proportion=1, flag=wx.EXPAND | wx.ALL | wx.ALIGN_LEFT)
        
        self.SetSizer(self.sizer)
        self.Fit()
        
        # Pubsubs
        self.callbacks = [("signals.ballotviewer.set_image_pil", self.pubsub_set_image_pil),
                          ("signals.ballotviewer.set_candidate_targets", self.pubsub_set_candidate_targets),
                          ("signals.ballotviewer.set_targets", self.pubsub_set_targets)]

    def subscribe_pubsubs(self):
        for (topic, callback) in self.callbacks:
            Publisher().subscribe(callback, topic)
        self.ballotscreen.subscribe_pubsubs()

    def unsubscribe_pubsubs(self):
        """
        Deactivate listeners that shouldn't be listening while this
        widget isn't active.
        """
        for (topic, callback) in self.callbacks:
            Publisher().unsubscribe(callback, topic)
        self.ballotscreen.unsubscribe_pubsubs()

    def set_image(self, imgpath):
        if not imgpath:
            self.toolbar.disable_buttons()
        else:
            self.toolbar.enable_buttons()
        self.ballotscreen.set_image(imgpath)
    def set_image_pil(self, path, img_pil):
        if not path or not img_pil:
            self.toolbar.disable_buttons()
        else:
            self.toolbar.enable_buttons()        
        self.ballotscreen.set_image_pil(path, img_pil)
    def get_imgsize(self):
        return (self.ballotscreen.img_bitmap.GetWidth(),
                self.ballotscreen.img_bitmap.GetHeight())
        
    #### Pubsub callbacks
    def pubsub_set_image_pil(self, msg):
        """ msg.data is a tuple: (str path, obj Image) """
        path, img_pil = msg.data
        self.set_image_pil(path, img_pil)
    def pubsub_set_candidate_targets(self, msg):
        target_locations, refimg_size_rel = msg.data
        self.ballotscreen.set_candidate_targets(target_locations, refimg_size_rel)
    def pubsub_set_targets(self, msg):
        target_locations = msg.data
        self.ballotscreen.set_targets(target_locations)
    
class ToolBar(wx.Panel):
    """
    Panel that displays all available tools (like create target,
    resize, zoom in, etc). No autodetect though (see gui.py for that)
    """
    # Restrict size of icons to 50 pixels height
    SIZE_ICON = 50.0
    
    def __init__(self, parent, *args, **kwargs):
        wx.Panel.__init__(self, parent, *args, **kwargs)

        # Instance vars
        self.parent = parent
        self.images = []
        self.iconsdir = os.path.join(MYDIR, 'imgs','icons')
        
        # vars for button states
        self.state_zoomin = False
        self.state_zoomout = False
        self.state_addtarget = False
        self.state_select = False
        self.state_addcontest = False
        self.state_splitcontest = False
        
        self._populate_icons(self.iconsdir)
        self._bind_events()
        
        ### PubSub Subscribing
        Publisher().subscribe(self._enter_autodetect, "signals.enter_autodetect")
        Publisher().subscribe(self._cancel_autodetect, "signals.cancel_autodetect")
        Publisher().subscribe(self._leave_autodetect_verify, "signals.leave_autodetect_verify")
        Publisher().subscribe(self._clear_buttons, "signals.Toolbar.clear_buttons")

    def _bind_events(self):
        self.btn_zoomin.Bind(wx.EVT_BUTTON, self.onButton_zoomin)
        self.btn_zoomin.Bind(wx.EVT_ENTER_WINDOW, self.onEnter_zoomin)
        self.btn_zoomin.Bind(wx.EVT_LEAVE_WINDOW, self.onLeave_zoomin)
        self.btn_zoomout.Bind(wx.EVT_BUTTON, self.onButton_zoomout)
        self.btn_zoomout.Bind(wx.EVT_ENTER_WINDOW, self.onEnter_zoomout)
        self.btn_zoomout.Bind(wx.EVT_LEAVE_WINDOW, self.onLeave_zoomout)
        self.btn_addtarget.Bind(wx.EVT_BUTTON, self.onButton_addtarget)
        self.btn_addtarget.Bind(wx.EVT_ENTER_WINDOW, self.onEnter_addtarget)
        self.btn_addtarget.Bind(wx.EVT_LEAVE_WINDOW, self.onLeave_addtarget)
        self.btn_select.Bind(wx.EVT_BUTTON, self.onButton_select)
        self.btn_select.Bind(wx.EVT_ENTER_WINDOW, self.onEnter_select)
        self.btn_select.Bind(wx.EVT_LEAVE_WINDOW, self.onLeave_select)
        self.btn_undo.Bind(wx.EVT_BUTTON, self.onButton_undo)
        self.btn_addcontest.Bind(wx.EVT_BUTTON, self.onButton_addcontest)
        self.btn_splitcontest.Bind(wx.EVT_BUTTON, self.onButton_splitcontest)
        self.btn_infercontests.Bind(wx.EVT_BUTTON, self.onButton_infercontests)
        self.btn_sanitycheck.Bind(wx.EVT_BUTTON, self.onButton_sanitycheck)
        
    def _resize_icons(self, iconpaths):
        """ Rescale all icon images to have height Toolbar.SIZE_ICON """
        bitmaps = {}
        for dirpath, dirnames, filenames in os.walk(iconpaths):
            for imgfile in [x for x in filenames if util_gui.is_image_ext(x)]:
                imgpath = os.path.join(dirpath, imgfile)
                wx_img = wx.Image(imgpath, wx.BITMAP_TYPE_ANY)
                c = wx_img.GetHeight() / ToolBar.SIZE_ICON
                wx_img = wx_img.Scale(wx_img.GetWidth() / c, wx_img.GetHeight() / c, wx.IMAGE_QUALITY_HIGH)
                bitmaps[util_gui.get_filename(imgpath)] = wx_img.ConvertToBitmap()
        return bitmaps
       
    def _populate_icons(self, iconsdir):
        bitmaps = self._resize_icons(iconsdir)
        self.bitmaps = bitmaps

        zoomin_unsel = bitmaps['zoomin_unsel']
        zoomin_sel = bitmaps['zoomin_sel']
        zoomout_unsel = bitmaps['zoomout_unsel']
        zoomout_sel = bitmaps['zoomout_sel']
        addtarget_unsel = bitmaps['addtarget_unsel']
        addtarget_sel = bitmaps['addtarget_sel']
        select_sel = bitmaps['select_sel']
        select_unsel = bitmaps['select_unsel']
        undo = bitmaps['undo']
        addcontest_unsel = bitmaps['addcontest_unsel']
        addcontest_sel = bitmaps['addcontest_sel']
        splitcontest_unsel = bitmaps['splitcontest_unsel']
        splitcontest_sel = bitmaps['splitcontest_sel']
        infercontest_unsel = bitmaps['infercontest_unsel']
        infercontest_sel = bitmaps['infercontest_sel']

        panel_zoomin = wx.Panel(self)
        panel_zoomout = wx.Panel(self)
        panel_addtarget = wx.Panel(self)
        panel_undo = wx.Panel(self)
        panel_addcontest = wx.Panel(self)
        panel_splitcontest = wx.Panel(self)
        panel_select = wx.Panel(self)
        panel_infercontest = wx.Panel(self)
        panel_sanitycheck = wx.Panel(self)
        self.btn_zoomin = wx.BitmapButton(panel_zoomin, bitmap=zoomin_unsel,
                                           id=wx.ID_ZOOM_IN,
                                           size=(zoomin_unsel.GetWidth()+8,
                                                 zoomin_unsel.GetHeight()+8),
                                          name='btn_zoomin')
        self.btn_zoomout = wx.BitmapButton(panel_zoomout, bitmap=zoomout_unsel,
                                            id=wx.ID_ZOOM_OUT,
                                            size=(zoomout_unsel.GetWidth()+8,
                                                  zoomout_unsel.GetHeight()+8),
                                           name='btn_zoomout')
        self.btn_addtarget = wx.BitmapButton(panel_addtarget, bitmap=addtarget_unsel,
                                       id=wx.ID_ANY,
                                       size=(addtarget_unsel.GetWidth()+8,
                                             addtarget_unsel.GetHeight()+8),
                                       name='btn_addtarget')
        self.btn_select = wx.BitmapButton(panel_select, bitmap=select_unsel,
                                          id=wx.ID_ANY,
                                          size=(select_unsel.GetWidth()+8,
                                                select_unsel.GetHeight()+8),
                                          name='btn_select')
        #self.btn_select.Hide()
        self.btn_addcontest = wx.BitmapButton(panel_addcontest, bitmap=addcontest_unsel,
                                              id=wx.ID_ANY,
                                              size=(addcontest_unsel.GetWidth()+8,
                                                    addcontest_unsel.GetHeight()+8),
                                              name='btn_addcontest')
        self.btn_splitcontest = wx.BitmapButton(panel_splitcontest, bitmap=splitcontest_unsel,
                                                id=wx.ID_ANY,
                                                size=(splitcontest_unsel.GetWidth()+8,
                                                      splitcontest_unsel.GetHeight()+8),
                                                name='btn_splitcontest')

        self.btn_undo = wx.BitmapButton(panel_undo, bitmap=undo,
                                        id=wx.ID_ANY,
                                        size=(undo.GetWidth()+8,
                                              undo.GetHeight()+8),
                                        name='btn_undo')
        self.btn_infercontests = wx.BitmapButton(panel_infercontest, bitmap=infercontest_unsel,
                                                id=wx.ID_ANY,
                                                size=(infercontest_unsel.GetWidth()+8,
                                                      infercontest_unsel.GetHeight()+8),
                                                name='btn_infercontest')
        self.btn_sanitycheck = wx.Button(panel_sanitycheck, label="Sanity Check...")

        font = wx.Font(8, wx.FONTFAMILY_DEFAULT, wx.FONTSTYLE_NORMAL, wx.FONTWEIGHT_NORMAL)
        sizer_zoomin = wx.BoxSizer(wx.VERTICAL)
        panel_zoomin.SetSizer(sizer_zoomin)
        txt1 = wx.StaticText(panel_zoomin, label="Zoom in", style=wx.ALIGN_CENTER)
        txt1.SetFont(font)
        sizer_zoomin.Add(self.btn_zoomin)
        sizer_zoomin.Add(txt1, flag=wx.ALIGN_CENTER)
        
        sizer_zoomout = wx.BoxSizer(wx.VERTICAL)
        panel_zoomout.SetSizer(sizer_zoomout)
        txt2 = wx.StaticText(panel_zoomout, label="Zoom out", style=wx.ALIGN_CENTER)
        txt2.SetFont(font)
        sizer_zoomout.Add(self.btn_zoomout)
        sizer_zoomout.Add(txt2, flag=wx.ALIGN_CENTER)

        sizer_addtarget = wx.BoxSizer(wx.VERTICAL)
        panel_addtarget.SetSizer(sizer_addtarget)
        txt3 = wx.StaticText(panel_addtarget, label="New voting target", style=wx.ALIGN_CENTER)
        txt3.SetFont(font)
        sizer_addtarget.Add(self.btn_addtarget)
        sizer_addtarget.Add(txt3, flag=wx.ALIGN_CENTER)

        sizer_undo = wx.BoxSizer(wx.VERTICAL)
        panel_undo.SetSizer(sizer_undo)
        txt4 = wx.StaticText(panel_undo, label="Undo", style=wx.ALIGN_CENTER)
        txt4.SetFont(font)
        sizer_undo.Add(self.btn_undo)
        sizer_undo.Add(txt4, flag=wx.ALIGN_CENTER)

        sizer_addcontest = wx.BoxSizer(wx.VERTICAL)
        panel_addcontest.SetSizer(sizer_addcontest)
        txt5 = wx.StaticText(panel_addcontest, label="Add New Contest", style=wx.ALIGN_CENTER)
        txt5.SetFont(font)
        sizer_addcontest.Add(self.btn_addcontest)
        sizer_addcontest.Add(txt5, flag=wx.ALIGN_CENTER)

        sizer_splitcontest = wx.BoxSizer(wx.VERTICAL)
        panel_splitcontest.SetSizer(sizer_splitcontest)
        txt6 = wx.StaticText(panel_splitcontest, label="Split a Contest", style=wx.ALIGN_CENTER)
        txt6.SetFont(font)
        sizer_splitcontest.Add(self.btn_splitcontest)
        sizer_splitcontest.Add(txt6, flag=wx.ALIGN_CENTER)

        sizer_select = wx.BoxSizer(wx.VERTICAL)
        panel_select.SetSizer(sizer_select)
        txt7 = wx.StaticText(panel_select, label="Select", style=wx.ALIGN_CENTER)
        txt7.SetFont(font)
        sizer_select.Add(self.btn_select)
        sizer_select.Add(txt7, flag=wx.ALIGN_CENTER)

        sizer_infercontest = wx.BoxSizer(wx.VERTICAL)
        panel_infercontest.SetSizer(sizer_infercontest)
        txt8 = wx.StaticText(panel_infercontest, label="Infer Contests", style=wx.ALIGN_CENTER)
        txt8.SetFont(font)
        sizer_infercontest.Add(self.btn_infercontests)
        sizer_infercontest.Add(txt8, flag=wx.ALIGN_CENTER)

        sizer_sanitycheck = wx.BoxSizer(wx.VERTICAL)
        panel_sanitycheck.SetSizer(sizer_sanitycheck)
        txt9 = wx.StaticText(panel_sanitycheck, label="Run Sanity Check...", style=wx.ALIGN_CENTER)
        txt9.SetFont(font)
        sizer_sanitycheck.Add(self.btn_sanitycheck)
        sizer_sanitycheck.Add(txt9, flag=wx.ALIGN_CENTER)

        self.sizer = wx.BoxSizer(wx.HORIZONTAL)
        self.sizer.Add(panel_zoomin)
        self.sizer.Add(panel_zoomout)
        self.sizer.Add(panel_addtarget)
        self.sizer.Add(panel_addcontest)
        self.sizer.Add(panel_splitcontest)
        self.sizer.Add(panel_undo)
        self.sizer.Add(panel_select)
        self.sizer.Add(panel_infercontest)
        self.sizer.Add(panel_sanitycheck)
        self.SetSizer(self.sizer)
        self.SetAutoLayout(1)
                          
    def clear_btns(self):
        self.state_zoomin = False
        self.state_zoomout = False
        self.state_addtarget = False
        self.state_select = False
        self.state_autodetect = False
        self.state_addcontest = False
        self.state_splitcontest = False
        self.btn_zoomin.SetBitmapLabel(self.bitmaps['zoomin_unsel'])
        self.btn_zoomout.SetBitmapLabel(self.bitmaps['zoomout_unsel'])
        self.btn_addtarget.SetBitmapLabel(self.bitmaps['addtarget_unsel'])
        self.btn_select.SetBitmapLabel(self.bitmaps['select_unsel'])
        self.btn_addcontest.SetBitmapLabel(self.bitmaps['addcontest_unsel'])
        self.btn_splitcontest.SetBitmapLabel(self.bitmaps['splitcontest_unsel'])
        self.btn_infercontests.SetBitmapLabel(self.bitmaps['infercontest_unsel'])
        
    #### PubSub Callbacks
    def _enter_autodetect(self, msg):
        self.disable_buttons()
    def _cancel_autodetect(self, msg):
        self.enable_buttons()
    def _leave_autodetect_verify(self, msg):
        self.enable_buttons()
    def _clear_buttons(self, msg):
        self.clear_btns()
        
    def select_button(self, name):
        mapping = {'addtarget': self.btn_addtarget,
                   'select': self.btn_select,
                   'zoomin': self.btn_zoomin,
                   'zoomout': self.btn_zoomout,
                   'addcontest': self.btn_addcontest,
                   'splitcontest': self.btn_splitcontest,
                   'infercontest': self.btn_infercontests}
        sel_bitmap = self.bitmaps[name+"_sel"]
        mapping[name].SetBitmapLabel(sel_bitmap)
        
    def enable_buttons(self):
        self.btn_zoomin.Enable()
        self.btn_zoomout.Enable()
        self.btn_addtarget.Enable()
        self.btn_select.Enable()
        self.btn_addcontest.Enable()
        self.btn_splitcontest.Enable()
        self.btn_infercontests.Enable()
    def disable_buttons(self, flag=None):
        if flag != "allow_zoom":
            self.btn_zoomin.Disable()
            self.btn_zoomout.Disable()
        self.btn_addtarget.Disable()
        self.btn_select.Disable()
        self.btn_addcontest.Disable()
        self.btn_splitcontest.Disable()
        self.btn_infercontests.Disable()
        
    #### Event handling
    def onButton_zoomin(self, event):
        Publisher().sendMessage("signals.BallotScreen.zoom", 'in')
        event.Skip()
    def onButton_zoomout(self, event):
        Publisher().sendMessage("signals.BallotScreen.zoom", 'out')
        event.Skip()
    def onButton_addtarget(self, event):
        if not self.state_addtarget:
            self.clear_btns()
            self.state_addtarget = True
            self.btn_addtarget.SetBitmapLabel(self.bitmaps['addtarget_sel'])
            Publisher.sendMessage("signals.BallotScreen.update_state", BallotScreen.STATE_ADD_TARGET)
        event.Skip()
    def onButton_select(self, event):
        if not self.state_select:
            self.clear_btns()
            self.state_select = True
            self.btn_select.SetBitmapLabel(self.bitmaps['select_sel'])
            Publisher().sendMessage("signals.BallotScreen.update_state", BallotScreen.STATE_IDLE)
        event.Skip()
    def onButton_undo(self, event):
        Publisher().sendMessage("broadcast.undo")
    def onButton_addcontest(self, event):
        if not self.state_addcontest:
            self.clear_btns()
            self.state_addcontest = True
            self.btn_addcontest.SetBitmapLabel(self.bitmaps['addcontest_sel'])
            Publisher().sendMessage("signals.BallotScreen.update_state", BallotScreen.STATE_ADD_CONTEST)
        event.Skip()
    def onButton_splitcontest(self, event):
        self.clear_btns()
        self.state_splitcontest = True
        self.btn_splitcontest.SetBitmapLabel(self.bitmaps['splitcontest_sel'])
        dlg = SplitContestDialog(self)
        self.Disable()
        exitval = dlg.ShowModal()
        self.Enable()
        if exitval == wx.ID_CANCEL:
            self.clear_btns()
            return
        splitmode = dlg.get_splitmode()
        Publisher().sendMessage("signals.BallotScreen.update_state", BallotScreen.STATE_SPLIT_CONTEST)
        Publisher().sendMessage("signals.BallotScreen.set_splitmode", splitmode)

    def onButton_infercontests(self, event):
        # Call SpecifyTargetsPanel.do_infer_contests
        self.parent.parent.do_infer_contests()

    def onButton_sanitycheck(self, event):
        result = self.parent.parent.sanity_check_grouping()
        if result == True:
            dlg = wx.MessageDialog(self, message="OpenCount wasn't able \
to find any incomplete blank ballots. However, this isn't a guarantee \
that all voting-targets have been detected. If you are confident that \
all voting targets have been detected, then it's safe to proceed to the \
next step.", style=wx.OK)
            self.Disable()
            dlg.ShowModal()
            self.Enable()
            
    def onEnter_zoomin(self, event):
        Publisher().sendMessage('signals.StatusBar.push', "Zoom into the opened image.")
        event.Skip()
    def onLeave_zoomin(self, event):
        Publisher().sendMessage('signals.StatusBar.pop', None)
        event.Skip()
    def onEnter_zoomout(self, event):
        Publisher().sendMessage('signals.StatusBar.push', "Zoom out of the opened image.")
        event.Skip()
    def onLeave_zoomout(self, event):
        Publisher().sendMessage('signals.StatusBar.pop', None)
        event.Skip()
    def onEnter_addtarget(self, event):
        Publisher().sendMessage('signals.StatusBar.push', "Create new voting targets.")
        event.Skip()
    def onLeave_addtarget(self, event):
        Publisher().sendMessage('signals.StatusBar.pop', None)
        event.Skip()
    def onEnter_select(self, event):
        Publisher().sendMessage('signals.StatusBar.push', 'Select voting targets.')
        event.Skip()
    def onLeave_select(self, event):
        Publisher().sendMessage('signals.StatusBar.pop', None)
        event.Skip()

class BallotScreen(ImageViewer):
    """
    Window that displays a ballot image, and lets the user create 
    voting target 'boxes'.
    Also, we will allow the user to draw bounding boxes around 
    contests.
    """
    
    # Constants used for Edit State
    STATE_IDLE = 0
    STATE_ADD_TARGET = 1
    STATE_MODIFY = 2
    STATE_AUTODETECT = 3
    STATE_AUTODETECT_VERIFY = 4
    STATE_ZOOM_IN = 5
    STATE_ZOOM_OUT = 6
    STATE_ADD_CONTEST = 7
    STATE_SPLIT_CONTEST = 8
    
    # Aux States
    STATE_RESIZE_TARGET = 9
    
    def __init__(self, parent, world, *args, **kwargs):
        ImageViewer.__init__(self, parent, world, *args, **kwargs)
        
        self._autodet_rect = None           # Coords of selected region (client coords)
        self._autodetect_region = None  # PIL Image of selected region 
        
        # Instance vars
        self.candidate_targets = None   # Stores list of autodetected targets-to-be-verified

        # _splitmode is for Split Contest, either 'horizontal' or 'vertical'
        self._splitmode = 'horizontal'
        
    def subscribe_pubsubs(self):
        ImageViewer.subscribe_pubsubs(self)
        callbacks = (("signals.BallotScreen.update_state", self._update_state),
                     ("signals.BallotScreen.new_image", self._new_image),
                     ("signals.enter_autodetect", self._enter_autodetect),
                     ("signals.cancel_autodetect", self._cancel_autodetect),
                     ("signals.enter_autodetect_verify", self._enter_autodetect_verify),
                     ("signals.leave_autodetect_verify", self._leave_autodetect_verify),
                     ("signals.BallotScreen.fit_autodetect_region", self._fit_autodetect_region),
                     ("signals.BallotScreen.set_targets", self.pubsub_set_targets),
                     ("signals.BallotScreen.set_contests", self._pubsub_set_contests),
                     ("signals.BallotScreen.set_bounding_boxes", self._pubsub_set_bounding_boxes),
                     ("signals.ballotscreen.remove_targets", self._pubsub_remove_targets),
                     ("signals.BallotScreen.set_splitmode", self._pubsub_set_splitmode))
        self.callbacks.extend(callbacks)
        for (topic, callback) in callbacks:
            Publisher().subscribe(callback, topic)
        
    def _bind_events(self):
        ImageViewer._bind_events(self)
        self.Bind(wx.EVT_KEY_DOWN, self.onKeyDown)

    def set_state(self, newstate):
        if newstate not in (BallotScreen.STATE_IDLE, 
                         BallotScreen.STATE_ADD_TARGET,
                         BallotScreen.STATE_MODIFY,
                         BallotScreen.STATE_AUTODETECT,
                         BallotScreen.STATE_ZOOM_IN,
                         BallotScreen.STATE_ZOOM_OUT,
                         BallotScreen.STATE_RESIZE_TARGET,
                         BallotScreen.STATE_AUTODETECT_VERIFY,
                         BallotScreen.STATE_ADD_CONTEST,
                         BallotScreen.STATE_SPLIT_CONTEST):
            print "Incorrect newstate provided:", newstate
            return
        oldstate = self.curstate
        self.curstate = newstate
        if oldstate == BallotScreen.STATE_MODIFY and newstate != BallotScreen.STATE_MODIFY:
            self.unselect_boxes()
            
        self.set_cursor(newstate)
        self.Refresh()
        
    def set_splitmode(self, mode):
        """
        Sets the mode of the 'Split Contest' feature, either:
            mode := 'horizontal'
            mode := 'vertical'
        """
        VALID_MODES = ('horizontal', 'vertical')
        assert mode in VALID_MODES
        self._splitmode = mode

    def _pubsub_set_splitmode(self, msg):
        self.set_splitmode(msg.data)

    def set_auxstate(self, newstate):
        self.auxstate = newstate
        self.set_cursor(newstate)
        
    def set_cursor(self, state):
        if state in (BallotScreen.STATE_ADD_TARGET, BallotScreen.STATE_ADD_CONTEST):
            c = wx.CURSOR_CROSS
        elif state == BallotScreen.STATE_MODIFY:
            c = wx.CURSOR_HAND
        elif state == BallotScreen.STATE_ZOOM_IN or state == BallotScreen.STATE_ZOOM_OUT:
            c = wx.CURSOR_MAGNIFIER
        elif state == BallotScreen.STATE_RESIZE_TARGET:
            if self._resize_mode in ('upper-left', 'lower-right'):
                c = wx.CURSOR_SIZENWSE
            elif self._resize_mode in ('top', 'bottom'):
                c = wx.CURSOR_SIZENS
            elif self._resize_mode in ('left', 'right'):
                c = wx.CURSOR_SIZEWE
            elif self._resize_mode in ('upper-right', 'lower-left'):
                c = wx.CURSOR_SIZENESW
            elif self._resize_mode == 'interior':
                c = wx.CURSOR_SIZING
            else:
                # no change
                return
        elif state == BallotScreen.STATE_SPLIT_CONTEST:
            c = wx.CURSOR_IBEAM
        else:
            c = wx.CURSOR_ARROW
        self.SetCursor(wx.StockCursor(c))

    def set_candidate_targets(self, target_locations):
        """
        Given a list of (relative) (x,y,w,h), update the current state.
        """
        candidates = []
        for (x,y,w,h) in target_locations:
            x2,y2 = x+w, y+h
            
            candidates.append(BoundingBox(x, y, x2, y2, color="Orange"))
        self.candidate_targets = candidates
        
    def remove_voting_targets(self):
        self.world.remove_voting_targets(self.current_imgpath)
    def remove_contests(self):
        self.world.remove_contests(self.current_imgpath)
        
    def set_targets(self, target_locations):
        """
        Given a list of BoundingBoxes, update the current state.
        Keep all previous contests though.
        """
        targets = []
        for box in target_locations:
            x1, y1, x2, y2 = box.get_coords()
            targets.append(BoundingBox(x1, y1, x2, y2, 
                                       color=box.color,
                                       id=box.id,
                                       contest_id=box.contest_id))
        self.remove_voting_targets()
        for b in targets:
            self.world.add_box(self.current_imgpath, b)
        
    def set_contests(self, contest_locations):
        """
        Given a list of BoundingBoxes, update the current state.
        Keep all previous voting targets though.
        """
        contests = []
        for box in contest_locations:
            x1, y1, x2, y2 = box.get_coords()
            contests.append(BoundingBox(x1, y1, x2, y2, 
                                        color=box.color, 
                                        is_contest=True,
                                        id=box.id,
                                        contest_id=box.contest_id))
        self.remove_contests()
        for b in contests:
            self.world.add_box(self.current_imgpath, b)
        
    def set_bounding_boxes(self, bounding_boxes):
        """
        Given a list of BoundingBoxes (which may be for voting targets
        or contests), update the current state.
        """
        self.world.set_boxes(self.current_imgpath, bounding_boxes)
        
    #### PubSub callbacks
        
    def _update_state(self, msg):
        self.set_state(msg.data)
    def _set_sel_target_size(self, msg):
        for box in self.get_selected_boxes():
            box.update_size(msg.data)
    def _global_resize(self, msg):
        newsize = msg.data
        for t in self.world.get_boxes(self.current_imgpath):
            t.update_size(newsize)
        for box in self.get_selected_boxes():
            box.update_size(newsize)
        self.Refresh()
    def _new_image(self, msg):
        """
        Happens when the user loads up a new image, File->Open...
        """
        filepath = msg.data
        self.set_image(filepath)
        self.set_state(BallotScreen.STATE_IDLE)
        self.Refresh()
    def _enter_autodetect(self, msg):
        self.set_state(BallotScreen.STATE_AUTODETECT)
        
    def _cancel_autodetect(self, msg):
        self.set_state(BallotScreen.STATE_IDLE)
        self._autodet_rect = None
    def _enter_autodetect_verify(self, msg):
        if self._autodetect_region:
            w_img, h_img = self.img_pil.size
            t_w_rel = (self._autodetect_region.size[0] / float(w_img))
            t_h_rel = (self._autodetect_region.size[1] / float(h_img))
            self.target_width, self.target_height = (int(round(t_w_rel * self.GetClientSize()[0])),
                                                     int(round(t_h_rel * self.GetClientSize()[1])))
            Publisher().sendMessage("signals.TargetDimPanel", (self.target_width, self.target_height))
            Publisher().sendMessage("signals.autodetect.final_refimg", self._autodetect_region)
            self.candidate_targets = self.autodetect_targets(self.img_pil, self._autodetect_region)
            #frame = Autodetect_Confirm(self, self.candidate_targets)
            #frame.Show()
            self.set_state(BallotScreen.STATE_AUTODETECT_VERIFY)
            #self.Refresh()
        else:
            print "Error -- in BallotScreen._enter_autodetect_verify, \
self._autodetect_region was None, i.e. the user didn't choose anything."
        
    def _leave_autodetect_verify(self, msg):
        # Clean up autodetect state, consolidate verified detected
        # targets (if necessary), restore state to IDLE
        if msg.data == 'remove_all':
            self.candidate_targets = None
        else:
            [t.set_color("Green") for t in self.candidate_targets]
            self.world.add_boxes(self.current_imgpath, self.candidate_targets)
        self.candidate_targets = None
        self._autodet_rect = None
        self._autodetect_region = None
        self.set_state(BallotScreen.STATE_IDLE)
        
    def _fit_autodetect_region(self, msg):
        if self._autodetect_region:
            self._autodetect_region = util_gui.fit_image(self._autodetect_region)
            Publisher().sendMessage("signals.autodetect.updatebox", 
                                    self._autodetect_region)
            Publisher().sendMessage("signals.TargetDimPanel", (self._autodetect_region.size))
        self.Refresh()
    def pubsub_set_targets(self, msg):
        imgpath, boxes = msg.data
        self.set_targets(boxes)
    def _pubsub_set_contests(self, msg):
        imgpath, boxes = msg.data
        self.set_contests(boxes)
    def _pubsub_set_bounding_boxes(self, msg):
        imgpath, boxes = msg.data
        self.set_bounding_boxes(boxes)
    def _pubsub_remove_targets(self, msg):
        targets = msg.data
        for t in targets:
            self.delete_target(t)
        self.Refresh()

    def select_target(self, t):
        ImageViewer.select_target(self, t)
        w_client, h_client = self.GetClientSize()
        Publisher().sendMessage("signals.TargetDimPanel._set_sel_target_size", (int(round(t.width*w_client)), int(round(t.height*h_client))))

    def autodetect_targets(self, img, refimg):
        """
        Autodetect Voting Targets - a reference image is given by
        'refimg', which is a PIL image. Image to search is given by
        'img', which is also a PIL image.
        """
        w_img, h_img = img.size
        w_refimg, h_refimg = refimg.size
        img_array = np.array(img)
        refimg_array = np.array(refimg)
        match_coords = util_gui.template_match(img_array, refimg_array, confidence=0.6)
        pts = []
        candidate_targets = []
        for x,y in match_coords:
            too_close = False
            for pt in pts:
                if util_gui.dist_euclidean((x,y), pt) <= 5.0:
                    too_close = True
                    break
            if too_close:
                continue
            pts.append((x,y))
            x_rel = x / float(w_img)
            y_rel = y / float(h_img)
            w_rel = w_refimg / float(w_img)
            h_rel = h_refimg / float(h_img)
            x2_rel, y2_rel = x_rel + w_rel, y_rel + h_rel
            candidate_targets.append(BoundingBox(x_rel, y_rel, x2_rel, y2_rel, color="Orange"))
        return candidate_targets

    def is_within_img(self, pos):
        """
        Return True if the user's mouse is actually within the displayed
        ballot image.
        """
        x,y = pos
        return (x < self.img_bitmap.GetWidth() and
                y < self.img_bitmap.GetHeight())
        
    #### Event handlers
    
    def onLeftDown(self, event):
        """
        Depending on the edit mode, either creates a new voting target
        box, or moves an existing voting target box (if the mouse is
        close to one).
        """
        self.SetFocus()
        x, y = self.CalcUnscrolledPosition(event.GetPositionTuple())
        if not self.is_within_img((x,y)):
            return
        # Resizing-handling events has precedence - no other
        # mouse-event handling should occur unless no resizing is
        # going on.
        if (self.curstate in (BallotScreen.STATE_IDLE, BallotScreen.STATE_MODIFY)):
            box, mode = self.get_closest_resize_box(self.world.get_boxes(self.current_imgpath), 
                                                    (x,y))
            if box and self.is_resize_enabled() and not self.get_selected_boxes():
                self.set_resize_target(box, mode)
                self._prev_auxstate = self.auxstate
                self.set_auxstate(BallotScreen.STATE_RESIZE_TARGET)
                self.Refresh()
                return
        if self.curstate in (BallotScreen.STATE_ADD_TARGET, BallotScreen.STATE_ADD_CONTEST):
            w_img, h_img = self.img_bitmap.GetWidth(), self.img_bitmap.GetHeight()
            x_rel, y_rel = x / float(w_img), y / float(h_img)
            w_rel, h_rel = 1.0 / float(w_img), 1.0 / float(h_img)
            x2_rel, y2_rel = x_rel + w_rel, y_rel + h_rel
            is_contest = self.curstate == BallotScreen.STATE_ADD_CONTEST
            new_box = BoundingBox(x_rel, y_rel, x2_rel, y2_rel, is_contest=is_contest)
            self.set_new_box(new_box)
            #self.world.add_box(self.current_imgpath, new_box)
            self.Refresh()
        elif (self.curstate in (BallotScreen.STATE_IDLE, BallotScreen.STATE_MODIFY)
                and self.get_closest_target((x,y),mode="interior")
                and self.is_modify_enabled()):
            # Select the relevant box to be moved
            mousepos = (x,y)
            closest_t = self.get_closest_target(mousepos, mode="interior")
            if closest_t in self.get_selected_boxes():
                # Don't unselect it
                self.enable_dragging()
                return
            elif self.get_selected_boxes():
                # Kick out previously selected boxes
                self.unselect_boxes()
            # Bring in the new box
            self.enable_dragging()
            self.select_target(closest_t)
            self.Refresh()
        elif (self.curstate in (BallotScreen.STATE_IDLE, BallotScreen.STATE_MODIFY)
              and self.is_modify_enabled()):
            # Start dragging a selection box
            assert len(self._dragselectregion) == 0, "dragselectregion wasn't empty."
            self._dragselectregion = [x,y,x+1,y+1]
            self.unselect_boxes()
            self.Refresh()
        elif (self.curstate == BallotScreen.STATE_SPLIT_CONTEST
              and self.is_modify_enabled()):
            contests = self.get_contests()
            c = self.get_closest_target((x,y), boxes=contests, mode="interior")
            if c:
                w_img, h_img = self.get_bitmapsize()
                x_rel = x / float(w_img)
                y_rel = y / float(h_img)
                res = split_contest((x_rel, y_rel), c, self.get_boxes(), mode=self._splitmode)
                try:
                    self.push_state(self.world)
                    c1, c2 = res
                    self.remove_box(c)
                    self.add_boxes((c1,c2))
                    contests = [b for b in self.get_boxes() if b.is_contest]
                    for target in [b for b in self.get_boxes() if not b.is_contest]:
                        target.contest_id = util_gui.find_assoc_contest(target, contests).contest_id
                    Publisher().sendMessage("broadcast.updated_world")
                    Publisher().sendMessage("broadcast.freeze_contest", (self.current_imgpath, c1))
                    Publisher().sendMessage("broadcast.freeze_contest", (self.current_imgpath, c2))
                    print "Split successful."
                    self.Refresh()
                except TypeError as e:
                    # Split wasn't possible
                    print "Split not successful."
                    traceback.print_exc()
                    pass
            else:
                pass
            self.Refresh()
        elif self.curstate == BallotScreen.STATE_AUTODETECT:
            self._autodet_rect = (x, y, x+1, y+1)
            self.Refresh()
        elif self.curstate == BallotScreen.STATE_ZOOM_IN:
            old_virt_pos = (x,y)
            old_scale = self.scale
            self.increase_scale(0.6)
            new_virt_pos = (x*(self.scale / old_scale), y*(self.scale / old_scale))
            self.center_viewport(new_virt_pos, event.GetPositionTuple())
            self.Refresh()
        elif self.curstate == BallotScreen.STATE_ZOOM_OUT:
            old_virt_pos = (x,y)
            old_scale = self.scale
            self.decrease_scale(0.6)
            new_virt_pos = (x*(self.scale / old_scale), y*(self.scale / old_scale))
            self.center_viewport(new_virt_pos, event.GetPositionTuple())
            self.Refresh()
        elif self.curstate == BallotScreen.STATE_AUTODETECT_VERIFY:
            closest_target = self.get_closest_target((x,y), boxes=self.candidate_targets, mode="bounding-box")
            if closest_target:
                self.candidate_targets.remove(closest_target)
            self.Refresh()
            
        closest_box, mode = self.get_closest_box_any(self.world.get_boxes(self.current_imgpath), (x,y))
        if (self.curstate in (BallotScreen.STATE_IDLE, BallotScreen.STATE_MODIFY)
                and not closest_box):
            # User clicked the 'background', i.e. an area with no
            # boxes, so unselect any selected box
            self.unselect_boxes()
            
    def onLeftUp(self, event):
        """ Drop the voting target box at the current mouse location. """
        mousepos = self.CalcUnscrolledPosition(event.GetPositionTuple())
        if (self.curstate in (BallotScreen.STATE_ADD_TARGET, BallotScreen.STATE_ADD_CONTEST)
                and self.is_new_box()):
            self.push_state(self.world)
            new_box = self.get_new_box()
            new_box = util_gui.standardize_box(new_box)
            self.unset_new_box()
            # I won't add new_box to world just yet - I want to first
            # auto-fit around it, then add the auto-cropped bounding
            # box to world
            if new_box.is_contest:
                Publisher().sendMessage("broadcast.ballotscreen.added_contest", 
                                        (self.current_imgpath, new_box))
            else:
                Publisher().sendMessage("broadcast.ballotscreen.added_target", 
                                        (self.current_imgpath, new_box))
            Publisher().sendMessage("broadcast.updated_world")
            self.Refresh()
        elif (self.curstate in (BallotScreen.STATE_IDLE, BallotScreen.STATE_MODIFY)
                and self.is_select_target()):
            moved_contests = [b for b in self._sel_boxes if b.is_contest]
            for contest in moved_contests:
                Publisher().sendMessage("broadcast.freeze_contest", (self.current_imgpath, contest))
            self.disable_dragging()
            self._dragselectregion = []
            Publisher().sendMessage("broadcast.updated_world")            
            self.Refresh()
        elif (self.curstate in (BallotScreen.STATE_IDLE, BallotScreen.STATE_MODIFY)
              and self._dragselectregion):
            x1, y1, x2, y2 = self._dragselectregion
            ul_corner, lr_corner = util_gui.get_box_corners((x1,y1), (x2,y2))
            dragselectregion = list(ul_corner + lr_corner)
            self._dragselectregion = []
            # Also select all boxes that lie within this
            w_img, h_img = self.get_bitmapsize()
            dragselectregion_rel = (dragselectregion[0] / float(w_img),
                                    dragselectregion[1] / float(h_img),
                                    dragselectregion[2] / float(w_img),
                                    dragselectregion[3] / float(h_img))
            boxes = util_gui.get_boxes_inside(self.get_boxes(), dragselectregion_rel)
            for box in boxes:
                self.select_target(box)
            Publisher().sendMessage("broadcast.updated_world")
            self.Refresh()
        elif (self.curstate == BallotScreen.STATE_AUTODETECT and self._autodet_rect):
            try:
                img = util_gui.open_as_grayscale(self.current_imgpath)
            except IOError:
                # Sometimes, a BMP file throws a PIL error: Unsupported BMP Compression,
                # but wxImage can open it just fine. Weird!
                img = util_gui.imageToPil(wx.Image(self.current_imgpath), flatten=True)
            x1, y1, x2, y2 = self._autodet_rect
            w_img, h_img = self.img_bitmap.GetWidth(), self.img_bitmap.GetHeight()
            x1 = int(round((x1 / float(w_img)) * img.size[0]))
            y1 = int(round((y1 / float(h_img)) * img.size[1]))
            x2 = int(round((x2 / float(w_img)) * img.size[0]))
            y2 = int(round((y2 / float(h_img)) * img.size[1]))
            region = img.crop(((x1,y1,x2,y2)))
            #region_threshold = util_gui.fit_image(region)
            
            self._autodetect_region = region
            Publisher().sendMessage("signals.autodetect.updatebox", self._autodetect_region)
        
        if self.is_resize_target() and self.is_resize_enabled():
            # Finalize the current resizing
            Publisher().sendMessage("broadcast.push_state", self.world)
            x, y = mousepos
            x1, y1, x2, y2 = self._resize_rect
            (ul_x, ul_y), (lr_x, lr_y) = util_gui.get_box_corners((x1, y1), (x2, y2))
            self._resize_target.x1 = ul_x / float(self.img_bitmap.GetWidth())
            self._resize_target.y1 = ul_y / float(self.img_bitmap.GetHeight())
            self._resize_target.x2 = lr_x / float(self.img_bitmap.GetWidth())
            self._resize_target.y2 = lr_y / float(self.img_bitmap.GetHeight())
            if not self._resize_target.is_contest:
                # Now update all other voting targets, since we want all voting
                # targets to have the same size.
                w_rel, h_rel = (abs(ul_x - lr_x) / float(self.img_bitmap.GetWidth()),
                        abs(ul_y - lr_y) / float(self.img_bitmap.GetHeight()))
                alltargets = [b for b in self.world.get_boxes_all_list() if not b.is_contest]
                util_gui.resize_boxes(alltargets, (w_rel, h_rel), self._resize_mode)
            if self._resize_target.is_contest:
                Publisher().sendMessage("broadcast.freeze_contest", (self.current_imgpath, self._resize_target))
            self.unset_resize_target()
            Publisher().sendMessage("broadcast.updated_world")
            self.set_auxstate(self._prev_auxstate)
            self._prev_auxstate = None
        self.Refresh()
        
    def onRightDown(self, event):
        """
        If the edit mode is 'Modify', then if the user right-clicks a
        voting target box, bring up a selection to modify it (say,
        dimensions of that particular box.
        Not sure if needed.
        """
        x,y = self.CalcUnscrolledPosition(event.GetPositionTuple())
        if (self.curstate == BallotScreen.STATE_MODIFY):
            mousepos = self.CalcUnscrolledPosition(event.GetPositionTuple())
            closest_t = self.get_closest_target(mousepos)
            if closest_t:
                print "Displaying a messagebox to modify dimensions of the \
selected box...in your imagination."
                self.select_target(closest_t)
        elif (self.curstate == BallotScreen.STATE_ZOOM_IN):
            old_virt_pos = (x,y)
            old_scale = self.scale
            
            self.decrease_scale(0.6)

            new_virt_pos = (x*(self.scale / old_scale), y*(self.scale / old_scale))
            
            self.center_viewport(new_virt_pos, event.GetPositionTuple())
            self.Refresh()
        elif self.curstate == BallotScreen.STATE_ZOOM_OUT:
            old_virt_pos = (x,y)
            old_scale = self.scale
            
            self.increase_scale(0.6)

            new_virt_pos = (x*(self.scale / old_scale), y*(self.scale / old_scale))
            
            self.center_viewport(new_virt_pos, event.GetPositionTuple())
            self.Refresh()            
        self.Refresh()

    def onMotion(self, event):
        """
        Depending on the edit mode, move the voting target box 
        currently held by the user.
        """
        x, y = self.CalcUnscrolledPosition(event.GetPositionTuple())
        if not self._oldmousepos:
            self._oldmousepos = x,y
            
        # Aux State Handling
        if self.is_resize_target() and self.is_resize_enabled():
            # Resizing takes precedence - no other mouse-handling
            # events should happen
            if self._resize_mode == 'left':
                self._resize_rect[0] = x
            elif self._resize_mode == 'top':
                self._resize_rect[1] = y
            elif self._resize_mode == 'right':
                self._resize_rect[2] = x
            elif self._resize_mode == 'bottom':
                self._resize_rect[3] = y
            elif self._resize_mode == 'upper-left':
                self._resize_rect[0] = x
                self._resize_rect[1] = y
            elif self._resize_mode == 'upper-right':
                self._resize_rect[2] = x
                self._resize_rect[1] = y
            elif self._resize_mode == 'lower-left':
                self._resize_rect[0] = x
                self._resize_rect[3] = y
            elif self._resize_mode == 'lower-right':
                self._resize_rect[2] = x
                self._resize_rect[3] = y
            self.Refresh()
            self._oldmousepos = (x,y)
            return            
            
        if (self.curstate in (BallotScreen.STATE_IDLE, BallotScreen.STATE_MODIFY)
                and self.is_select_target() and event.LeftIsDown()
                and self.can_drag() and self.is_modify_enabled()):
            # The user is currently moving a box
            w_img, h_img = self.img_bitmap.GetWidth(), self.img_bitmap.GetHeight()
            x_rel, y_rel = x / float(w_img), y / float(h_img)
            x_delta = x_rel - (self._oldmousepos[0] / float(w_img))
            y_delta = y_rel - (self._oldmousepos[1] / float(h_img))
            for box in self.get_selected_boxes():
                box.x1 += x_delta
                box.y1 += y_delta
                box.x2 += x_delta
                box.y2 += y_delta
            self._oldmousepos = (x,y)
            self.Refresh()
        elif (self.curstate in (BallotScreen.STATE_ADD_TARGET, BallotScreen.STATE_ADD_CONTEST)
                and self.is_new_box() and event.LeftIsDown()):
            # I am in the middle of resizing a newly-created box
            w_img, h_img = self.img_bitmap.GetWidth(), self.img_bitmap.GetHeight()
            x_rel, y_rel = x / float(w_img), y / float(h_img)
            self._new_box.x2 = x_rel
            self._new_box.y2 = y_rel
            self._new_box.set_color("Red")
            self.Refresh()
        elif (self.curstate in (BallotScreen.STATE_IDLE, BallotScreen.STATE_MODIFY)
              and self._dragselectregion and event.LeftIsDown()):
            # User is currently click-dragging a selection box
            x1, y1, x2, y2 = self._dragselectregion
            self._dragselectregion[2] = x
            self._dragselectregion[3] = y
            self.Refresh()
        elif (self.curstate == BallotScreen.STATE_AUTODETECT):
            if event.LeftIsDown() and self._autodet_rect:
                x1, y1 = self._autodet_rect[0], self._autodet_rect[1]
                x2, y2 = x, y
                self._autodet_rect = (x1, y1, x2, y2)
                self.Refresh()
        elif (self.curstate in (BallotScreen.STATE_IDLE, BallotScreen.STATE_MODIFY)
                and not self.is_resize_target()
                and not self._resize_cursor_flag):
            # Chcek to see if we need to change mouse cursor
            t, mode = self.get_closest_box_any(self.world.get_boxes(self.current_imgpath), (x,y))
            if t:
                if mode in ('upper-left', 'lower-right') and self.is_resize_enabled():
                    myCursor = wx.StockCursor(wx.CURSOR_SIZENWSE)
                elif mode in ('top', 'bottom') and self.is_resize_enabled():
                    myCursor = wx.StockCursor(wx.CURSOR_SIZENS)
                elif mode in ('left', 'right') and self.is_resize_enabled():
                    myCursor = wx.StockCursor(wx.CURSOR_SIZEWE)
                elif mode in ('upper-right', 'lower-left') and self.is_resize_enabled():
                    myCursor = wx.StockCursor(wx.CURSOR_SIZENESW)
                elif mode == 'interior' and self.is_modify_enabled():
                    myCursor = wx.StockCursor(wx.CURSOR_SIZING)
                else:
                    # we're not updating the cursor
                    return
                self._prev_cursor = self.GetCursor()
                self.SetCursor(myCursor)
                self._resize_cursor_flag = True
                self.Refresh()
        elif (self.curstate in (BallotScreen.STATE_IDLE, BallotScreen.STATE_MODIFY)
                and not self.is_resize_target()
                and self._resize_cursor_flag):
            # Check to see if we need to revert mouse cursor
            t, mode = self.get_closest_box_any(self.world.get_boxes(self.current_imgpath), (x,y))
            if not t:
                self.SetCursor(self._prev_cursor)
                self._prev_cursor = wx.StockCursor(wx.CURSOR_ARROW)
                self._resize_cursor_flag = False
                self.Refresh()
                
        # Update oldmousepos
        self._oldmousepos = (x,y)
        event.Skip()
        
    def onKeyDown(self, event):
        keycode = event.GetKeyCode()
        if (self.curstate in (BallotScreen.STATE_IDLE, BallotScreen.STATE_MODIFY)
                and self.get_selected_boxes()):
            if ((keycode == wx.WXK_DELETE or keycode == wx.WXK_BACK) 
                    and self.is_delete_enabled()
                    and self.is_modify_enabled()):
                Publisher().sendMessage("broadcast.push_state", self.world)
                deleted_boxes = self.get_selected_boxes()
                for box in self.get_selected_boxes()[:]:
                    self.delete_target(box)
                
                Publisher().sendMessage("broadcast.updated_world")
                Publisher().sendMessage("broadcast.deleted_targets", (self.current_imgpath, deleted_boxes))
            elif ((keycode in (wx.WXK_UP, wx.WXK_DOWN, wx.WXK_LEFT, wx.WXK_RIGHT))
                  and self.is_modify_enabled()):
                w_img, h_img = self.img_bitmap.GetWidth(), self.img_bitmap.GetHeight()
                for box in self.get_selected_boxes():
                    if keycode == wx.WXK_UP:
                        box.y1 = max(0.0, box.y1 - (1.0 / h_img))
                        box.y2 -= (1.0 / h_img)
                    elif keycode == wx.WXK_DOWN:
                        box.y1 = min(h_img-1, box.y1 + (1.0 / h_img))
                        box.y2 = min(h_img-1, box.y2 + (1.0 / h_img))
                    elif keycode == wx.WXK_LEFT:
                        box.x1 = max(0.0, box.x1 - (1.0 / w_img))
                        box.x2 -= (1.0 / w_img)
                    elif keycode == wx.WXK_RIGHT:
                        box.x1 = min(w_img-1, box.x1 + (1.0 / w_img))
                        box.x2 = min(w_img-1, box.x2 + (1.0 / w_img))
                self.Refresh()
                return  # To avoid event.Skip() propagating to scrollbars
        self.Refresh()
        event.Skip()

    def onPaint(self, event):
        """ 
        Refresh screen. 
        Note: Regrettably, I couldn't simply call the inherited 
              onPaint() method of the parent, since visual things got
              all wonky.
        """
        if self.IsDoubleBuffered():
            dc = wx.PaintDC(self)
        else:
            dc = wx.BufferedPaintDC(self)
        # You must do PrepareDC in order to force the dc to account
        # for scrolling.
        self.PrepareDC(dc)
        
        dc.DrawBitmap(self.img_bitmap, 0, 0)
        self._display_targets(dc)
        if self.curstate == BallotScreen.STATE_AUTODETECT and self._autodet_rect:
            self._draw_autodet_rect(dc)
        if self.is_resize_target():
            self._draw_resize_rect(dc)
        if self.curstate == BallotScreen.STATE_AUTODETECT_VERIFY:
            self._draw_candidate_targets(dc, self.candidate_targets)
        if self._dragselectregion:
            self._draw_dragselectregion(dc)
        event.Skip()
        
    def _draw_autodet_rect(self, dc):
        dc.SetBrush(wx.TRANSPARENT_BRUSH)
        dc.SetPen(wx.Pen("Green", 3))
        x1, y1, x2, y2 = self._autodet_rect
        (ul_x, ul_y), (lr_x, lr_y) = util_gui.get_box_corners((x1, y1), (x2, y2))
        w, h = abs(lr_x - ul_x), abs(lr_y - ul_y)
        dc.DrawRectangle(ul_x, ul_y, w, h)
        
    def _draw_resize_rect(self, dc):
        dc.SetBrush(wx.TRANSPARENT_BRUSH)
        dc.SetPen(wx.Pen("Orange", 3))
        x1, y1, x2, y2 = self._resize_rect
        (ul_x, ul_y), (lr_x, lr_y) = util_gui.get_box_corners((x1, y1), (x2, y2))
        w, h = abs(lr_x - ul_x), abs(lr_y - ul_y)
        dc.DrawRectangle(ul_x, ul_y, w, h)
        
    def _draw_candidate_targets(self, dc, candidate_targets):
        dc.SetBrush(wx.TRANSPARENT_BRUSH)
        for t in candidate_targets:
            self._draw_box(dc, t)
            
    def _display_targets(self, dc):
        """ Only to be called from self.onPaint(2) """
        dc.SetBrush(wx.TRANSPARENT_BRUSH)
        if self.current_imgpath:
            targets = [t for t in self.world.get_boxes(os.path.abspath(self.current_imgpath)) if not t.is_contest]
            contests = [t for t in self.world.get_boxes(os.path.abspath(self.current_imgpath)) if t.is_contest]
            if self.is_new_box() and not self._new_box.is_contest:
                targets.append(self._new_box)
            elif self.is_new_box() and self._new_box.is_contest:
                contests.append(self._new_box)
            for t in targets:
                c = t.contest_id
                self._draw_box(dc, t)
            for t in contests:
                c = t.contest_id
                self._draw_box(dc, t)

class Autodetect_Panel(wx.Panel):
    """
    Frame that pops up when user clicks 'Autodetect'
    """
    def __init__(self, parent, *args, **kwargs):
        #wx.Frame.__init__(self, parent, title="Autodetect Voting Targets Frame")
        wx.Panel.__init__(self, parent, *args, **kwargs)
        font = wx.Font(12, wx.MODERN, style=wx.NORMAL, weight=wx.NORMAL, underline=False)
        txt_inst = wx.StaticText(self, label="""
Please highlight an example voting target 
from the ballot image, (by clicking-and-dragging),
and click 'Continue' to proceed with auto-detection.""", style=wx.ALIGN_CENTRE)
        txt_inst.SetFont(font)
        self.panel_btns = wx.Panel(self)
        self.panel_btns.sizer = wx.BoxSizer(wx.HORIZONTAL)
        btn_continue = wx.Button(self.panel_btns, label="Continue")
        btn_continue.Bind(wx.EVT_BUTTON, self.onButton_continue)
        btn_cancel = wx.Button(self.panel_btns, label="Cancel")
        btn_cancel.Bind(wx.EVT_BUTTON, self.onButton_cancel)
        self.panel_btns.sizer.Add(btn_continue, flag=wx.ALIGN_CENTRE)
        self.panel_btns.sizer.Add(btn_cancel, flag=wx.ALIGN_CENTRE)
        self.panel_btns.SetSizer(self.panel_btns.sizer)
        self.sizer = wx.BoxSizer(wx.VERTICAL)
        
        help_gif = 'imgs/help/autodetect.gif'
        self.ag = wx.animate.GIFAnimationCtrl(self, wx.ID_ANY, help_gif, pos=(0,0))
        self.ag.GetPlayer().UseBackgroundColour(True)
        self.ag.Play()
        # self.staticbmp represents the image region currently selected
        self.staticbmp = wx.StaticBitmap(self, size=(100, 100))
        # Set to True when user selects target for the first time
        self._did_user_select = False
        self.btn_fit = wx.Button(self, label="Fit Autodetect Region")
        self.sizer.Add(txt_inst, flag=wx.ALIGN_CENTER)
        self.sizer.Add(self.ag, flag=wx.ALIGN_CENTER)
        self.sizer.Add(self.staticbmp, flag=wx.ALIGN_CENTER)
        self.sizer.Add(self.btn_fit, flag=wx.ALIGN_CENTER)
        self.sizer.Add(self.panel_btns, flag=wx.ALIGN_CENTER)
        
        self.Bind(wx.EVT_WINDOW_DESTROY, self.onWindowDestroy)
        self.btn_fit.Bind(wx.EVT_BUTTON, self.onButton_fit)
        
        # Set to True if I destroy myself (vs. system destroying it)
        self._did_i_destroy = None
        
        self.SetSizer(self.sizer)
        self.Fit()
        self.rect_coords = None
        
        # PubSub Subscribing
        Publisher().subscribe(self._boxupdate, "signals.autodetect.updatebox")
        
    #### Pubsub Callbacks
    def _boxupdate(self, msg):
        """ Receives a PIL image """
        img_pil = msg.data
        w_img, h_img = img_pil.size
        c = h_img / 100.0
        new_w = int(round(w_img / c))
        bmp = util_gui.PilImageToWxBitmap(img_pil.resize((new_w, 100), Image.ANTIALIAS))
        #self.staticbmp.SetSize((100, min(new_h, 20)))
        self.staticbmp.SetBitmap(bmp)
        self.Refresh()
        self.Fit()
        if not self._did_user_select:
            self._did_user_select = True
        
    def onButton_continue(self, event):
        if self._did_user_select:
            Publisher().sendMessage("signals.enter_autodetect_verify", None)
        else:
            Publisher().sendMessage("signals.cancel_autodetect", None)
        self._did_i_destroy = True
        event.Skip()
    def onButton_cancel(self, event):
        Publisher().sendMessage("signals.cancel_autodetect", None)
        self._did_i_destroy = True
    def onButton_fit(self, event):
        Publisher().sendMessage("signals.BallotScreen.fit_autodetect_region", None)
        event.Skip()
        
    def onWindowDestroy(self, event):
        # Question: Does this get called even after a 'successful'
        # autodetect run? I'd prefer that a 'cleanup' routine not
        # be invoked twice during 'normal' usage.
        if self._did_i_destroy != True:
            Publisher.sendMessage("signals.cancel_autodetect", None)
        event.Skip()


class Autodetect_Confirm(wx.Panel):
    def __init__(self, parent, target_candidates, *args, **kwargs):
        wx.Panel.__init__(self, parent, *args, **kwargs)
        
        # Set to True iff I destroy myself (vs. system destroying me)
        self._did_i_destroy = None
        
        #self.SetTitle("Verify Autodetected Targets")
        self.panel = wx.Panel(self)
        font = wx.Font(12, wx.MODERN, wx.NORMAL, wx.NORMAL, underline=False)
        txt = wx.StaticText(self.panel, label=
"""{0} targets were detected. You may either 
delete specific targets by clicking on the 
offending target, or proceed by choosing 'Done.'""".format(len(target_candidates)), style=wx.ALIGN_CENTRE)
        txt.SetFont(font)

        self.panel_btn = wx.Panel(self.panel)
        btn_done = wx.Button(self.panel_btn, label="Done")
        btn_removeall = wx.Button(self.panel_btn, label="Remove all.")
        self.panel_btn.sizer = wx.BoxSizer(wx.HORIZONTAL)
        self.panel_btn.sizer.Add(btn_done, flag=wx.ALIGN_CENTER)
        self.panel_btn.sizer.Add(btn_removeall, flag=wx.ALIGN_CENTER)
        self.panel_btn.SetSizer(self.panel_btn.sizer)
        
        self.panel.sizer = wx.BoxSizer(wx.VERTICAL)
        self.panel.sizer.Add(txt, flag=wx.ALIGN_CENTER)
        self.panel.sizer.Add(self.panel_btn, flag=wx.ALIGN_CENTER)
        self.panel.SetSizer(self.panel.sizer)
        
        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.sizer.Add(self.panel)

        btn_done.Bind(wx.EVT_BUTTON, self.onButtonDone)
        btn_removeall.Bind(wx.EVT_BUTTON, self.onButtonRemoveAll)
        self.Bind(wx.EVT_WINDOW_DESTROY, self.onWindowDestroy)
        
        self.SetSizer(self.sizer)
        self.Fit()
    def onButtonDone(self, evt):
        self._did_i_destroy = True
        Publisher().sendMessage("signals.leave_autodetect_verify")
        #self.Destroy()
    def onButtonRemoveAll(self, evt):
        self._did_i_destroy = True
        Publisher().sendMessage("signals.leave_autodetect_verify", 'remove_all')
        #self.Destroy()
    def onWindowDestroy(self, evt):
        if self._did_i_destroy != True:
            Publisher().sendMessage("signals.leave_autodetect_verify", 'remove_all')
        evt.Skip()
        
def split_contest(mousepos, contest, boxes, mode='horizontal'):
    """
    Depending on where the user clicked, split the contest in half,
    returning two contests:
        One contest that contains all targets to the left of the 
        mouse, and another contest that contains all targets to
        the right of the mouse.
    If the user clicked in a way such that no targets are to the
    left/right, then this will return the original contest, since
    there's nothing to split.
    Input:
        tuple mousepos: A tuple of floats, in relative coords (x,y)
        obj contest: A BoundingBox instance for a contest.
        list boxes: A list of BoundingBoxes for the entire template.
        str mode: Either 'horizontal' or 'vertical'. Split horizontally or
                  vertically.
    Output:
        Two contests if a split is possible - else, the original
        contest.
    """
    def get_contest_box(group):
        """
        Given a list of BoundingBoxes, return a contest bounding box
        that encompasses all boxes in group.
        """
        min_x1 = min([x1 for (x1,y1,x2,y2) in [b.get_coords() for b in group]])
        min_y1 = min([y1 for (x1,y1,x2,y2) in [b.get_coords() for b in group]])
        max_x2 = max([x2 for (x1,y1,x2,y2) in [b.get_coords() for b in group]])
        max_y2 = max([y2 for (x1,y1,x2,y2) in [b.get_coords() for b in group]])
        min_x1 = max(0, min_x1 - 0.05)
        min_y1 = max(0, min_y1 - 0.025)
        max_x2 = min(1.0, max_x2 + 0.05)
        max_y2 = min(1.0, max_y2 + 0.025)
        c = BoundingBox(min_x1, min_y1, max_x2, max_y2, is_contest=True)
        return c
    targets = util_gui.associated_targets(contest, [b for b in boxes if not b.is_contest])
    x, y = mousepos
    if mode == 'horizontal':
        left, right = [], []
        for b in targets:
            if b.x1 < x:
                left.append(b)
            else:
                right.append(b)
        if len(left) == len(targets) or len(right) == len(targets):
            # No split is possible
            return contest
        else:
            c_left = get_contest_box(left)
            c_right = get_contest_box(right)
            return c_left, c_right
    else:
        top, bottom = [], []
        for b in targets:
            if b.y1 < y:
                top.append(b)
            else:
                bottom.append(b)
        if len(top) == len(targets) or len(bottom) == len(targets):
            return contest
        else:
            c_top = get_contest_box(top)
            c_bottom = get_contest_box(bottom)
            return c_top, c_bottom

class SplitContestDialog(wx.Dialog):
    MODE_HORIZONTAL = 'horizontal'
    MODE_VERTICAL = 'vertical'

    def __init__(self, parent, *args, **kwargs):
        wx.Dialog.__init__(self, parent, *args, **kwargs)
        self.parent = parent
        self.splitmode = SplitContestDialog.MODE_HORIZONTAL
        txt = wx.StaticText(self, label="In what direction would you \
like to split the contest?")
        self.radiobtn_horizontal = wx.RadioButton(self, label="Split Horizontally", style=wx.RB_GROUP)
        self.radiobtn_vertical = wx.RadioButton(self, label="Split Vertically")
        self.radiobtn_horizontal.SetValue(True)
        btn_ok = wx.Button(self, id=wx.ID_OK)
        btn_ok.Bind(wx.EVT_BUTTON, self.onButton_ok)
        btn_cancel = wx.Button(self, id=wx.ID_CANCEL)
        btn_cancel.Bind(wx.EVT_BUTTON, self.onButton_cancel)
        
        sizer_btns = wx.BoxSizer(wx.HORIZONTAL)
        sizer_btns.Add(btn_ok)
        sizer_btns.Add(btn_cancel)

        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.SetSizer(self.sizer)
        self.sizer.Add(txt)
        self.sizer.Add(self.radiobtn_horizontal)
        self.sizer.Add(self.radiobtn_vertical)
        self.sizer.Add(sizer_btns)

        self.Fit()
        
    def get_splitmode(self):
        return self.splitmode

    def onButton_ok(self, evt):
        if self.radiobtn_horizontal.GetValue():
            self.splitmode = SplitContestDialog.MODE_HORIZONTAL
        else:
            self.splitmode = SplitContestDialog.MODE_VERTICAL
        self.EndModal(wx.ID_OK)
    def onButton_cancel(self, evt):
        self.EndModal(wx.ID_CANCEL)

class MainFrame(wx.Frame):
    """
    Demo Frame to quickly test the ImageViewer
    """
    def __init__(self, parent, screen=ImageViewer, *args, **kwargs):
        wx.Frame.__init__(self, parent, title="Demo ImageViewer",
                          style=wx.DEFAULT_FRAME_STYLE, 
                          *args, **kwargs)
        self.parent = parent
        self.world = WorldState()
        self.viewer = screen(self, self.world)
        self.btn_zoomin = wx.Button(self, label="Zoom in")
        self.btn_zoomin.Bind(wx.EVT_BUTTON, self.zoomin)
        self.btn_zoomout = wx.Button(self, label="Zoom out")
        self.btn_zoomout.Bind(wx.EVT_BUTTON, self.zoomout)
        btn_killvert = wx.Button(self, label="Kill vert scrollbar")
        btn_killvert.Bind(wx.EVT_BUTTON, self.kill_vertscroll)
        btn_sizer = wx.BoxSizer(wx.HORIZONTAL)
        btn_sizer.Add(self.btn_zoomin)
        btn_sizer.Add(self.btn_zoomout)
        btn_sizer.Add(btn_killvert)
        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.sizer.Add(self.viewer, proportion=1, flag=wx.EXPAND)
        self.sizer.Add(btn_sizer)
        
        self.SetSizer(self.sizer)
        self.Move((0,0))

    def zoomin(self, evt):
        self.viewer.zoom_and_center(1.2)
    def zoomout(self, evt):
        self.viewer.zoom_and_center(0.8)
        
    def kill_vertscroll(self, evt):
        xamt, yamt = self.viewer.GetScrollPixelsPerUnit()
        self.viewer.SetScrollbars(xamt, 0, 10.0, 10.0)

def main():
    args = sys.argv
    app = wx.App(False)
    if len(args) >= 3:
        screen = BallotScreen
    else:
        screen = ImageViewer
    frame = MainFrame(None, screen=screen)
    if len(args) >= 2:
        imgpath = args[1]
        img = Image.open(imgpath).convert('L')
        frame.viewer.set_image_pil(imgpath, img)
    frame.Show()
    app.MainLoop()
            
if __name__ == '__main__':
    main()
