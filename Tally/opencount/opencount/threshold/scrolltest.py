
import wx

class Test(wx.ScrolledWindow):
    def __init__(self, parent):
        wx.ScrolledWindow.__init__(self, parent, -1)
    def setup(self):
        wx.StaticText(self, -1, "asdfasdfasdf")
        self.SetScrollbars(20,20,55,65536*1024)
        

class MyScrolledWindow(wx.Frame):
   def __init__(self, parent, id, title):
       wx.Frame.__init__(self, parent, id, title, size=(500, 400))

       sw = Test(self)
       sw.setup()
       #bmp = wx.Image('aliens.jpg',wx.BITMAP_TYPE_JPEG).ConvertToBitmap()
       #wx.StaticBitmap(sw, -1, bmp)

class MyApp(wx.App):
   def OnInit(self):
       frame = MyScrolledWindow(None, -1, 'Aliens')
       frame.Show(True)
       frame.Centre()
       return True

app = MyApp(0)
app.MainLoop()
