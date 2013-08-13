import sys, os

import wx, Image
from wx.lib.scrolledpanel import ScrolledPanel

import grouping.make_overlays as make_overlays

TXT_NUMIMGS = 'Number of images:'

class OverlayPanel(ScrolledPanel):
    def __init__(self, parent, *args, **kwargs):
        ScrolledPanel.__init__(self, parent, *args, **kwargs)
        self.parent = parent

        self.imgpaths = []

        sizer = wx.BoxSizer(wx.VERTICAL)
        
        self.txt_numimgs = wx.StaticText(self, label="{0} 0".format(TXT_NUMIMGS))
        sizer.Add(self.txt_numimgs)

        imgsizer = wx.BoxSizer(wx.HORIZONTAL)
        self.min_img = wx.StaticBitmap(self)
        self.max_img = wx.StaticBitmap(self)
        imgsizer.Add(self.min_img)
        imgsizer.Add(self.max_img)

        sizer.Add(imgsizer)
        
        self.SetSizer(sizer)
        self.Fit()

        self.SetupScrolling()

    def update_txt_numimgs(self):
        self.txt_numimgs.SetLabel("{0} {1}".format(TXT_NUMIMGS, len(self.imgpaths)))

    def start(self, imgpaths, do_align=True):
        """ Displays the images given by imgpaths. """
        self.imgpaths = imgpaths
        # 0.) Create min/max overlays, optionally aligning
        minimg, maximg = make_overlays.make_minmax_overlay(imgpaths, do_align=do_align, rszFac=0.75)
        h, w = minimg.shape
        # 1.) Convert numpy array to wxImage
        min_wxbmp = wx.EmptyBitmap(w, h)
        max_wxbmp = wx.EmptyBitmap(w, h)
        min_pilimg = Image.fromarray(minimg).convert("RGB")
        max_pilimg = Image.fromarray(maximg).convert("RGB")
        min_wxbmp.CopyFromBuffer(min_pilimg.tostring())
        max_wxbmp.CopyFromBuffer(max_pilimg.tostring())
        self.min_img.SetBitmap(min_wxbmp)
        self.max_img.SetBitmap(max_wxbmp)

        self.update_txt_numimgs()

        self.Layout()
        self.Refresh()

def isimgext(f):
    return os.path.splitext(f)[1].lower() in ('.png', '.jpg', '.jpeg')

class SimpleOverlayFrame(wx.Frame):
    def __init__(self, parent, imgpaths, *args, **kwargs):
        wx.Frame.__init__(self, parent, *args, **kwargs)
        self.parent = parent
        self.imgpaths = imgpaths

        sizer = wx.BoxSizer(wx.VERTICAL)

        self.overlaypanel = OverlayPanel(self)
        btn_go = wx.Button(self, label="Create Overlays")
        btn_go.Bind(wx.EVT_BUTTON, self.onButton_go)
        self.chkbox_doalign = wx.CheckBox(self, label="Perform alignment?")

        btn_sizer = wx.BoxSizer(wx.HORIZONTAL)
        btn_sizer.Add(btn_go)
        btn_sizer.Add(self.chkbox_doalign)
        
        sizer.Add(self.overlaypanel, proportion=1, flag=wx.EXPAND)        
        sizer.Add(btn_sizer, flag=wx.ALIGN_CENTER)

        self.SetSizer(sizer)

    def onButton_go(self, evt):
        do_align = self.chkbox_doalign.GetValue()
        print 'Doing alignment?', do_align
        self.overlaypanel.start(self.imgpaths, do_align=do_align)

def main():
    args = sys.argv[1:]
    imgsdir = args[0]
    imgpaths = []
    for dirpath, dirnames, filenames in os.walk(imgsdir):
        for imgname in [f for f in filenames if isimgext(f)]:
            imgpaths.append(os.path.join(dirpath, imgname))
    
    app = wx.App(False)
    frame = SimpleOverlayFrame(None, imgpaths)
    frame.Show()
    app.MainLoop()    
    

if __name__ == '__main__':
    main()

                            
        
