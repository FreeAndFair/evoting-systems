import subprocess
import glib
import gobject
import gtk
import pdb
import os
from signal import SIGKILL

class Requestor(object):
    def __init__(self,cmdline_array,
                 stdout_cb = None,
                 stderr_cb = None,
                 hup_cb = None, 
                 data = None,
                 stdout_cb_data = None):
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
        self.stdout_cb_data = stdout_cb_data
        self.start()

    def start(self):
        self.p= subprocess.Popen(self.cmdline_array,
                                 bufsize = 0,
                                 stdin=subprocess.PIPE,
                                 stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE)
        (self.stdin,self.stdout,self.stderr) = (
            self.p.stdin,self.p.stdout,self.p.stderr)
        self.pid = self.p.pid
        self.stdout_watch_id = glib.io_add_watch(
            self.p.stdout,glib.IO_IN,self.receive_stdout,self.data)
        self.stderr_watch_id = glib.io_add_watch(
            self.p.stderr,glib.IO_IN,self.receive_stderr,self.data)
        #if self.hup_cb is not None:
        self.hup_watch_id = glib.io_add_watch(
            self.p.stdout,glib.IO_HUP,self.receive_hup, None)

    def stop(self):
        os.kill(self.p.pid,SIGKILL)
        self.p = None
        glib.source_remove(self.stdout_watch_id)
        glib.source_remove(self.stderr_watch_id)
        glib.source_remove(self.hup_watch_id)


    def send(self,data):
        self.stdin.write(data)
        self.stdin.flush()
        #print "REQ sent",data
        return True

    def receive_stdout(self,fd,condition,status):
        # call receive callback if provided
        # then handle case where not provided
        
        char = fd.read(1)
        self.stdout_line = self.stdout_line + char
        if char == '\n':
            if self.stdout_cb is not None:
                (self.stdout_cb)(self.stdout_line,self.stdout_cb_data)
            #print self.stdout_line
            #self.stdout.flush()
            self.stdout_line = ""
        return True

    def receive_stderr(self,fd,condition,status):
        # call receive callback if provided
        # then handle case where not provided
        char = fd.read(1)
        self.stderr_line = self.stderr_line + char
        if char == '\n':
            if self.stderr_cb is not None:
                (self.stderr_cb)()
            print "STDERR: "+self.stderr_line
            self.stdout.flush()
            self.stderr = ""
        return True

    def receive_hup(self,fd,condition,status):
        # call receive callback if provided
        # then handle case where not provided
        if self.hup_cb is not None:
            (self.hup_cb)()
        print "HUP"
        self.stdout.flush()
        #gobject.source_remove(timeout)
        return False

