import os, sys, pdb
try:
    import cPickle as pickle
except:
    import pickle
import wx, wx.lib.scrolledpanel
sys.path.append('..')

class LabelPanel(wx.lib.scrolledpanel.ScrolledPanel):
    """
    A panel that allows you to, given a set of images I, give a text
    label to each image. Outputs to an output file.
    """

    def __init__(self, parent, *args, **kwargs):
        wx.lib.scrolledpanel.ScrolledPanel.__init__(self, parent, *args, **kwargs)
        self.parent = parent
        
        # self.imagelabels keeps track of the labels that the user has
        # given to each image.
        self.imagelabels = {}   # maps {imagepath: str label}

        # self.imagecaptions keeps track of the caption that the UI 
        # should display to the user.
        self.imagecaptions = {} # maps {imagepath: str caption}

        # self.captionlabels keeps track of all labels given to a
        # specific caption.
        self.captionlabels = {} # maps {str caption: [str label_i, ...]}

        self.imagepaths = []  # ordered list of imagepaths
        self.cur_imgidx = 0  # which image we're currently at

        self.outpath = 'labelpanelout.csv'

        self.callback = None
        self.possibles = None

        self._init_ui()

    def _init_ui(self):
        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.SetSizer(self.sizer)

        self.sizer2 = wx.BoxSizer(wx.HORIZONTAL)
        self.imgpatch = wx.StaticBitmap(self)

        self.txt_inst = wx.StaticText(self, label="Please enter the label for this image.")
        labeltxt = wx.StaticText(self, label='Label:')
        self.inputctrl = wx.TextCtrl(self, style=wx.TE_PROCESS_ENTER, size=(250,-1))
        self.inputctrl.Bind(wx.EVT_TEXT_ENTER, self.onInputEnter, self.inputctrl)
        nextbtn = wx.Button(self, label="Next")
        prevbtn = wx.Button(self, label="Previous")
        nextbtn.Bind(wx.EVT_BUTTON, self.onButton_next)
        prevbtn.Bind(wx.EVT_BUTTON, self.onButton_prev)
        donebtn = wx.Button(self, label="I'm Done.")
        donebtn.Bind(wx.EVT_BUTTON, self.onButton_done)
        inputsizer = wx.BoxSizer(wx.HORIZONTAL)
        inputsizer.Add(labeltxt)
        inputsizer.Add(self.inputctrl)
        self.progress_txt = wx.StaticText(self, label='')
        self.btn_sizer = wx.BoxSizer(wx.VERTICAL)
        self.btn_sizer.Add(self.txt_inst)
        self.btn_sizer.Add(inputsizer)
        self.btn_sizer.Add(nextbtn)
        self.btn_sizer.Add(prevbtn)
        self.btn_sizer.Add(donebtn)
        self.btn_sizer.Add(self.progress_txt)

        sizer_img = wx.BoxSizer(wx.VERTICAL)
        sizer_img.Add(self.imgpatch, proportion=0)
        self.caption_txt = wx.StaticText(self, label="Foo.")
        sizer_img.Add(self.caption_txt)

        sizer_lstbox = wx.BoxSizer(wx.VERTICAL)
        txt_listbox = wx.StaticText(self, label="Previously entered \
values for this caption...")
        self.listbox = wx.ListBox(self, choices=[])

        sizer_lstbox.Add(txt_listbox)
        sizer_lstbox.Add(self.listbox, flag=wx.EXPAND)

        self.sizer2.Add(self.btn_sizer, proportion=0)
        self.sizer2.Add((40, 40))
        self.sizer2.Add(sizer_lstbox)
        
        self.sizer.Add(sizer_img)
        self.sizer.Add(self.sizer2, proportion=1, flag=wx.EXPAND)

    def update_caption_txt(self, imgidx):
        """ Updates the self.caption_txt StaticText widget. """
        if imgidx >= len(self.imagepaths):
            print "Uh oh, imgidx out of range."
            print "== Press 'c' to continue."
            pdb.set_trace()
            return
        imgpath = self.imagepaths[imgidx]
        if imgpath in self.imagecaptions:
            caption = self.imagecaptions[imgpath]
            self.caption_txt.SetLabel("Caption: {0}.".format(caption))

    def update_listbox(self, imgidx):
        """ Updates the self.listbox ListBox widget, and displays all
        previously-entered labels that have the same caption.
        """
        if imgidx >= len(self.imagepaths):
            print "Uh oh, imgidx out of range."
            print "== Press 'c' to continue."
            pdb.set_trace()
            return
        imgpath = self.imagepaths[imgidx]
        if imgpath in self.imagecaptions:
            caption = self.imagecaptions[imgpath]
            labels = self.captionlabels.get(caption, None)
            if labels == None:
                self.listbox.SetItems(['No values entered.'])
                return
            self.listbox.SetItems(list(set(labels)))
        else:
            # Just display /all/ labels.
            self.listbox.SetItems(list(set(self.imagelabels.values())))

    def add_label(self, imgpath, label):
        """ Adds the 'label' for the given image by updating internal
        data structures. Returns True if it's valid, False o.w.
        """
        if self.possibles and label not in self.possibles:
            return False
        oldlabel = self.imagelabels[imgpath]
        self.imagelabels[imgpath] = label
        if oldlabel == label:
            return True
        caption = self.imagecaptions.get(imgpath, None)
        if caption != None:
            try:
                self.captionlabels[caption].remove(oldlabel)
            except:
                pass
            self.captionlabels.setdefault(caption, []).append(label)
        return True

    def onInputEnter(self, evt):
        """ Triggered when the user hits 'enter' when inputting text.
        """
        curimgpath = self.imagepaths[self.cur_imgidx]
        cur_val = self.inputctrl.GetValue()
        if not self.add_label(curimgpath, cur_val):
            dlg = wx.MessageDialog(self, message="Invalid value entered: {0}".format(cur_val),
                                   style=wx.OK)
            self.Disable()
            dlg.ShowModal()
            self.Enable()
            return
        else:
            if (self.cur_imgidx+1) >= len(self.imagepaths):
                self.onButton_done(None)
                return
            self.display_img(self.cur_imgidx + 1)

    def onButton_next(self, evt):
        curimgpath = self.imagepaths[self.cur_imgidx]
        cur_val = self.inputctrl.GetValue()
        if not self.add_label(curimgpath, cur_val):
            dlg = wx.MessageDialog(self, message="Invalid value entered: {0}".format(cur_val),
                                   style=wx.OK)
            self.Disable()
            dlg.ShowModal()
            self.Enable()
        if (self.cur_imgidx+1) >= len(self.imagepaths):
            return
        else:
            self.display_img(self.cur_imgidx + 1)
            
    def onButton_prev(self, evt):
        curimgpath = self.imagepaths[self.cur_imgidx]
        cur_val = self.inputctrl.GetValue()
        if not self.add_label(curimgpath, cur_val):
            dlg = wx.MessageDialog(self, message="Invalid value entered: {0}".format(cur_val),
                                   style=wx.OK)
            self.Disable()
            dlg.ShowModal()
            self.Enable()
        if self.cur_imgidx <= 0:
            return
        else:
            self.display_img(self.cur_imgidx - 1)

    def onButton_done(self, evt):
        dlg = wx.MessageDialog(self, message="Are you sure you're done?",
                               style=wx.YES_NO | wx.NO_DEFAULT)
        self.Disable()
        status = dlg.ShowModal()
        self.Enable()
        if status == wx.ID_YES:
            self.done()

    def done(self):
        """ Called when the user is finished labeling all images. """
        print "Labelling Done."
        # Make sure we don't lose the value of the current-label
        curimgpath = self.imagepaths[self.cur_imgidx]
        curval = self.inputctrl.GetValue()
        if not self.add_label(curimgpath, curval):
            dlg = wx.MessageDialog(self, message="Invalid value entered: {0}".format(curval),
                                   style=wx.OK)
            self.Disable()
            dlg.ShowModal()
            self.Enable()
        elif self.callback:
            self.callback(self.imagelabels)

    def reset(self):
        """ Resets my state to a 'clean' slate. """
        # TODO: Reset UI also.
        self.imagelabels = {}
        self.imagepaths = []
        self.imagecaptions = {}
        self.captionlabels = {}
        self.cur_imgidx = 0

    def start(self, imageslist, captions=None, callback=None, outfile='labelpanelout.csv',
              possibles=None):
        """Given a dict of imagepaths to label, set up the UI, and
        allow the user to start labeling things. This will reset all
        state to be a 'clean slate'.
        Input:
            lst imageslist: list of image paths
            dict captions: A dict mapping {str imgpath: str caption}.
                           If you want to display some caption for an
                           image to the user, provide it here.
            fn callback: If given, self.done() will call this function,
                         passing in the labelling results:
                             {str imgpath: str label}
            outfile: Output file to write results to.
            iter possibles: An iterable containing the possible values the
                user can input (optional).
        """
        self.captions = captions
        captions = captions if captions != None else {}
        self.possibles = possibles
        self.callback = callback
        self.reset()
        for imgpath in imageslist:
            if imgpath in self.imagelabels:
                print "Uhoh, imgpath was already in self.imagelabels. \
Implies that imgpath is present in imageslist more than once."
                print "    imgpath is:", imgpath
                print "    self.imagelabels[imgpath] is:", self.imagelabels[imgpath]
                pdb.set_trace()
            if imgpath in self.imagepaths:
                print "Uhoh, imgpath was already self.imagepaths. \
Implies that imgpath is present in imageslist more than once."
                print "    imgpath is:", imgpath
                pdb.set_trace()
            assert imgpath not in self.imagelabels
            assert imgpath not in self.imagepaths
            self.imagelabels[imgpath] = ''
            self.imagepaths.append(imgpath)
            caption = captions.get(imgpath, "An Image.")
            self.imagecaptions[imgpath] = caption

        self.cur_imgidx = 0
        self.display_img(self.cur_imgidx)

        #self.SetClientSize(self.parent.GetClientSize())
        self.SetupScrolling()
        self.SendSizeEvent()

    def restore_session(self, statefile):
        """ Tries to restore the state of a previous session. If this
        fails (say, the internal state file was deleted), then this
        will return False. If this happens, then you should just call
        self.start().
        """
        if not os.path.exists(statefile):
            return False
        state = pickle.load(open(statefile, 'rb'))
        imagelabels = state['imagelabels']
        imagepaths = state['imagepaths']

        ## TODO: Legacy-handling code follows.
        if 'imagecaptions' not in state:
            state['imagecaptions'] = {}
        if 'captionlabels' not in state:
            state['captionlabels'] = {}
        # END Legacy-handling code.

        self.imagelabels = imagelabels
        self.imagepaths = imagepaths
        self.imagecaptions = state['imagecaptions']
        self.captionlabels = state['captionlabels']
        self.cur_imgidx = 0
        self.display_img(self.cur_imgidx, no_overwrite=True)
        #self.SetClientSize(self.parent.GetClientSize())
        self.SetupScrolling()
        self.SendSizeEvent()
        #self.Fit()

        return True

    def save_session(self, statefile):
        """ Saves the current state of the current session. """
        # Remember to store the currently-displayed label
        curimgpath = self.imagepaths[self.cur_imgidx]
        cur_label = self.inputctrl.GetValue()
        self.imagelabels[curimgpath] = cur_label
        state = {}
        state['imagelabels'] = self.imagelabels
        state['imagepaths'] = self.imagepaths
        state['imagecaptions'] = self.imagecaptions
        state['captionlabels'] = self.captionlabels
        f = open(statefile, 'wb')
        pickle.dump(state, f)
        f.close()

    def display_img(self, idx, no_overwrite=False):
        """Displays the image at idx, and allow the user to start labeling
        it. Also updates the progress_txt.
        Input:
            int idx: Idx into self.imagepaths of the image to display.
            bool no_overwrite: If True, then this will /not/ store the
                current text in the text input (self.inputctrl) into
                our internal data structures (self.imagelabels). This
                is useful (albeit a bit of a hack) within
                self.restore_session().
        """
        if not (idx < len(self.imagepaths)):
            pdb.set_trace()
        assert idx < len(self.imagepaths)
        if not no_overwrite:
            # First, store current input into our dict
            old_imgpath = self.imagepaths[self.cur_imgidx]
            cur_input = self.inputctrl.GetValue()
            self.imagelabels[old_imgpath] = cur_input

        self.cur_imgidx = idx
        imgpath = self.imagepaths[self.cur_imgidx]
        wximg = wx.Image(imgpath, wx.BITMAP_TYPE_ANY)
        w_win, h_win = self.GetClientSize()
        w_new = min(wximg.GetWidth(), int(round(0.6*w_win)))
        c = wximg.GetWidth() / float(w_new)
        h_new = wximg.GetHeight() / c
        wximg_scaled = wximg.Scale(w_new, h_new, quality=wx.IMAGE_QUALITY_HIGH)
        bitmap = wx.BitmapFromImage(wximg_scaled)
        #bitmap = wx.Bitmap(imgpath, type=wx.BITMAP_TYPE_PNG)
        self.imgpatch.SetBitmap(bitmap)
        if h_new >= (h_win * 0.75):
            self.sizer.SetOrientation(wx.HORIZONTAL)
        else:
            self.sizer.SetOrientation(wx.VERTICAL)
        self.progress_txt.SetLabel("Currently viewing: Patch {0}/{1}".format(self.cur_imgidx+1,
                                                                             len(self.imagepaths)))
        self.inputctrl.SetValue(self.imagelabels[imgpath])
        self.update_caption_txt(self.cur_imgidx)
        self.update_listbox(self.cur_imgidx)
        #self.Fit()
        self.SetupScrolling()
        
    def export_labels(self):
        """ Exports all labels to an output csvfile. """
        f = open(self.outpath, 'w')
        header = ('imgpath', 'label')
        dictwriter = csv.DictWriter(f, header)
        util_gui._dictwriter_writeheader(f, header)
        for imgpath, label in self.imagelabels.iteritems():
            row = {'imgpath': imgpath, 'label': label}
            dictwriter.write_row(row)
        f.close()
