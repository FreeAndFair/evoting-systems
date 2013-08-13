import wx

def tab_wrap(towrap):
    def fn(CLAZZ, ARGS):
        class Result(wx.Panel):
            def __init__(self, *k, **w):
                p = k[0] if len(k) > 0 else w['parent']
                #print "PARENT", p
                #print "SSS", p.GetSize()
                w['size'] = p.GetSize()
                wx.Panel.__init__(self, p, size=p.GetSize())
                if k != []:
                    k = [self] + list(k[1:])
                sizer = wx.BoxSizer(wx.HORIZONTAL)
                ARGS[0] = (k, w)
                CLAZZ[0] = towrap(*k, **w)
                sizer.Add(CLAZZ[0])
                self.SetSizer(sizer)
                
                self.Fit()
                self.Refresh()
        
            def reset_panel(self):
                CLAZZ[0].reset_panel()
                CLAZZ[0].Destroy()
                CLAZZ[0] = towrap(*ARGS[0][0], **ARGS[0][1])
                self.GetSizer().Add(CLAZZ[0])
        
            def reset_data(self):
                CLAZZ[0].reset_data()
        
            def __getattr__(self, name):
                #print "GET", name
                return getattr(CLAZZ[0], name)
        
            def __setattr__(self, name, val):
                #print "SETTTING", name, val
                setattr(CLAZZ[0], name, val)
        return Result
    return fn([None], [None])
