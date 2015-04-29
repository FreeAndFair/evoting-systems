import subprocess
import glib
import gobject
import gtk
import pdb
from tevsgui_requestor import Requestor

class ScanRequestor(Requestor):
    def __init__(self,image_loc_fmt_string,stdout_cb=None,stderr_cb=None,hup_cb=None,data=None,duplex=False,heightmm=280,res=150,endorser=False,stdout_cb_data=None):
        self.image_loc_fmt_string = image_loc_fmt_string
        self.duplex = duplex
        self.heightmm = heightmm
        self.res = res
        self.endorser = endorser
        cmdline_array = ["/usr/bin/python","tevsgui_scan.py",str(duplex),str(heightmm),str(res),str(endorser),self.image_loc_fmt_string]
        #cmdline_array = ["/usr/bin/python","tevsgui_generic_client.py"]
        print cmdline_array
        super(ScanRequestor,self).__init__(
            cmdline_array,
            stdout_cb = stdout_cb,
            stderr_cb = stderr_cb,
            hup_cb = hup_cb, 
            data = data,
            stdout_cb_data = None)
        self.stdout_line = ""
        self.stderr_line = ""



class gui(object):
    def __init__(self):
        self.window = gtk.Window()
        self.window.show()
        self.svc = ScanRequestor("/tmp/%06d.jpg",
                               duplex=True,
                               heightmm=280,
                               res=300,
                               endorser=True)
        print "Svc",self.svc


if __name__ == "__main__":
    gui1 = gui()
    gtk.main()
