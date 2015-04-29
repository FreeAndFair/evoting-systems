import subprocess
import glib
import gobject
import gtk
import pdb

global sendnext 
global timeout
sendnext = "54321x12345"
timeout = None
global outstr
outstr = ""

#def my_receive_stdout(fd,condition,data):
#    print "In receive stdout"
#    if condition == glib.IO_IN:
#        print condition, glib.IO_IN
#        char = fd.read(1)
#        print char
#    return True

class Requestor(object):
    def __init__(self,cmdline_array,
                 stdout_cb = None,
                 stderr_cb = None,
                 hup_cb = None, 
                 data = None):
        self.p = None
        self.pid = None
        self.stdin = None
        self.stdout = None
        self.stderr = None
        self.stdout_cb = stdout_cb
        self.stderr_cb = stderr_cb
        self.hup_cb = hup_cb
        self.stdout_watch_id = None
        self.stderr_watch_id = None
        self.hup_watch_id = None
        self.cmdline_array = cmdline_array
        self.data = data
        self.start()

    def start(self):
        self.p= subprocess.Popen(self.cmdline_array,
                                 bufsize = 0,
                                 close_fds = True,
                                 stdin=subprocess.PIPE,
                                 stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT)
        #(self.stdin,self.stdout,self.stderr) = (
        #    self.p.stdin,self.p.stdout,self.p.stderr)
        self.pid = self.p.pid
        self.stdout_watch_id = glib.io_add_watch(
            self.p.stdout,glib.IO_IN,self.receive_stdout,self.data)
        #if self.hup_cb is not None:
        self.hup_watch_id = glib.io_add_watch(
            self.p.stdout,glib.IO_HUP,self.receive_hup, None)

    def stop():
        pass

    def send(self,data):
        data = "yabba\ndabba\r\n"
        self.p.stdin.write(data)
        self.p.stdin.flush()
        print "Generic svc sent",data,"down pipe",self.p.stdin
        #self.p.stdin.close()
        return True

    def receive_stdout(self,fd,condition,status):
        # call receive callback if provided
        # then handle case where not provided
        global outstr
        if condition == glib.IO_IN:
            char = fd.read(1)
            #print char
            outstr = "%s%s" % (outstr,char)
            if char=="\n":
                if self.stdout_cb is not None:
                    self.stdout_cb(outstr)
                    outstr = ""
        return True

    def receive_stderr(self,fd,condition,status):
        # call receive callback if provided
        # then handle case where not provided
        char = fd.read(1)
        print "E",char,
        return True

    def receive_hup(self,fd,condition,status):
        # call receive callback if provided
        # then handle case where not provided
        print "HUP"
        return False


if __name__ == "__main__":
    svc = Requestor(["/usr/bin/python","tevsgui_generic_client.py"])
    w = gtk.Window()
    b = gtk.Button()
    w.add(b)
    w.show_all()
    gtk.main()
                  
