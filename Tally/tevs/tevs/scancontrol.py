#!/usr/bin/env python

import const
import config
import pygtk
pygtk.require('2.0')
import gtk
import gobject
import select
import subprocess
import os
import pdb

def timeout_func(app):
    try:
        if app.pid:
            readable, writeable, exceptional = select.select([app.process_output_pipe.fileno()], [], [], 1)
            if len(readable)>0:
                x = app.process_output_pipe.readline()
                app.label.set_text(x)
        else:
            app.label.set_text("Not scanning.")
    except Exception, e:
        print e
    return True

class App():

    timeout = None
    process_object = None
    process_output_pipe = None
    pid = 0
    extractionpid = 0
    label = None

    def button1_cb(self, button, data):
        if App.pid:
            os.kill(App.pid, 9)
            App.pid = 0
            App.process_object = None
        p = subprocess.Popen(["/usr/bin/python", "-u",
                              "scanloop.py",
                              "-r",str(const.template_dpi),
                              "-l", str(int(const.ballot_height_inches)),
                              "-d", const.duplex],
                             stdout = subprocess.PIPE)
        App.process_object = p
        App.process_output_pipe = p.stdout
        print p.stdout
        print p.stdout.fileno()
        App.pid = p.pid
        print "Scanner at %d dpi, process id %d" % (const.template_dpi, App.pid)
        App.label.set_text("Will scan at %d dpi" % (const.template_dpi,))

    def button2_cb(self, button, data):
        if App.pid:
            os.kill(App.pid, 9)
            App.pid = 0
            App.process_object = None
        entrytext = App.entry1.get_text()
        entrytext = entrytext.replace('"', '').replace("'", "")
        if len(entrytext)>0:
            entrytext = '"'+entrytext+'"'
        p = subprocess.Popen(["/usr/bin/python", "-u",
                              "scanloop.py",
                              "-r", str(const.ballot_dpi),
                              "-l", str(int(const.ballot_height_inches)),
                              "-d", const.duplex,
                              "-c", App.entry1.get_text()],
                             stdout = subprocess.PIPE)
        App.process_object = p
        App.pid = p.pid
        App.process_output_pipe = p.stdout
        #print "Scanner at %d dpi, process id %d" % (const.ballot_dpi, App.pid)
        App.label.set_text("Will scan at %d dpi" % (const.ballot_dpi,))

    def button3_cb(self, button, data):
        if App.pid:
            os.kill(App.pid, 9)
            App.pid = 0
            App.process_object = None
            App.label.set_text("Ending scan process #%d" % App.pid)
        else:
            print "(No process to end.)"

    def button4_cb(self, button, data):
        self.button3_cb(button,data)
        gtk.main_quit()

    def __init__(self, topwindow):
        """Create app"""
        try:
            p = subprocess.Popen(["/usr/bin/scanimage", "-L"],
                                 stdout = subprocess.PIPE)
            scanner_model = p.stdout.readline()
        except Exception, e:
            print e
            scanner_model = "Problem locating scanner."
        App.root = topwindow
        vbox = gtk.VBox()
        App.root.add(vbox)
        if const.duplex == "True":
            dup_mode_str = "scan both sides"
        else:
            dup_mode_str = "scan only one side"
        toplabel_text = """Please note: 
Modes, sizes, and resolutions cannot be adjusted here, 
but may be altered by changing settings in tevs.cfg.

Mode: %s
Folder path: %s
Scanner: %s
""" % (dup_mode_str,const.incoming,scanner_model)
        button1 = gtk.Button("Scan templates (%d dpi)" % (const.template_dpi))
        button2 = gtk.Button("Scan ballots (%d dpi)" % (const.ballot_dpi))
        button3 = gtk.Button("Stop scanner")
        button4 = gtk.Button("Finished")
        entrylabel = gtk.Label("Comment, if any, to store with scans:")
        App.entry1 = gtk.Entry(80)
        App.entry1.set_text("")
        
        App.label = gtk.Label("Status")
        toplabel = gtk.Label(toplabel_text)
        vbox.pack_start(button1)
        vbox.pack_start(button2)
        vbox.pack_start(button3)
        vbox.pack_start(button4)
        vbox.pack_start(entrylabel)
        vbox.pack_start(App.entry1)
        vbox.pack_start(toplabel)
        vbox.pack_start(App.label)

        # If you want to simultaneously process/extract votes...
        #extraction = subprocess.Popen(["/usr/bin/python",
        #                      "main.py"])
        #App.extractionpid = extraction.pid
        #print "Started image processing subsystem, pid", App.extractionpid


        button1.connect("clicked", self.button1_cb, None)
        button2.connect("clicked", self.button2_cb, None)
        button3.connect("clicked", self.button3_cb, None)
        button4.connect("clicked", self.button4_cb, None)
        App.timeout = gobject.timeout_add(1500, timeout_func, self)


def on_delete_event(widget, event):
   return True

if __name__ == '__main__':
    config.get("tevs.cfg")
    window = gtk.Window(gtk.WINDOW_TOPLEVEL)
    #window.connect("delete-event", on_delete_event)
    window.set_title("Scanner Control")
    app = App(window)
    window.show_all()
    gtk.main()

