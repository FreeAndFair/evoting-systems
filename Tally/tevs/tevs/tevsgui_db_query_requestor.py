import subprocess
import glib
import gobject
import gtk
import pdb
import sys
from tevsgui_requestor import Requestor
import pickle

#TODO: user can be a read only user, or we can add an argument 
#      forcing read only access via alternate user/role

class QueryRequestor(Requestor):
    def __init__(self,stdout_cb=None,stderr_cb=None,hup_cb=None,query=None,user=None,database=None,retfile=None,stdout_cb_data=None):
        self.user = user
        self.database = database
        # put the data (request) in a command file and pass that to 
        # a small program which pickles results and calls us back
        cmdline_array = ["/usr/bin/python",
                         "tevsgui_db.py",
                         database,
                         user,
                         query,
                         retfile]
        print cmdline_array
        self.stdout_line = ""
        self.stderr_line = ""
        self.stdout_cb_data = stdout_cb_data
        super(QueryRequestor,self).__init__(
            cmdline_array,
            stdout_cb = stdout_cb,
            stderr_cb = stderr_cb,
            hup_cb = hup_cb, 
            data = query,
            stdout_cb_data = stdout_cb_data)

class gui(object):
    def __init__(self):
        self.window = gtk.Window()
        self.window.show()
        self.req = QueryRequestor(database=sys.argv[1],user=sys.argv[2],query=sys.argv[3],retfile=sys.argv[4],hup_cb = self.svc_cb)
        print "Requestor",self.req

    def svc_cb(self):
        print "Requestor done"
        data = pickle.load(open(sys.argv[4],"r"))
        print data


if __name__ == "__main__":
    gui1 = gui()
    gtk.main()

