#!/usr/bin/env python

import pygtk
pygtk.require('2.0')
import gtk
import subprocess
import os

introduction = """This DVD contains free software enabling you to demonstrate TEVS, the Trachtenberg Election Verification System.  In addition to TEVS, it includes sample ballot images of two different designs: Hart Intercivic and ESS. Each set of sample ballot images is included at two different scanning resolutions.

TEVS is copyright 2009, 2010, 2011 Mitch Trachtenberg and is licensed under the GNU General Public License version 3.

In addition to TEVS and the sample images, this DVD includes the Ubuntu variant of the Linux operating system, the Postgres SQL database program, the Python programming language, and other useful software (see the Applications menu).

Each "Count" button invokes TEVS using a different configuration file, which points TEVS to different image locations.  Once ballots have been counted and processed, you may display the ballots with TEVS' vote interpretation overlaid upon them by clicking the "Display" button.  You can show the source and processed files yourself by going to the out directory in your Home Folder.  You can go into the database tables yourself by running the psql program and using the following commands, each of which will open a SQL client on the specified database: psql hart150 or psql hart300 or psql seq150 or psql seq300 or psql scanned.  """

count_message = """Ballot images are now being counted.  As the system encounters each new ballot layout (often corresponding to a precinct), it generates definition files so that it may quickly count additional ballots of that layout.  The count stores results on a per-ballot basis. When the count is completed, we will display a summary of the results.  Pressing the Display button will then allow you to see the results as an overlay on each processed ballot. 
"""

display_message = """If you've counted these ballot images, you can now see the vote results overlaid on each counted ballot image.  Enter the image number and press Enter or click the Go button, then advance to the next image with the > button.
"""

def tevspath(*path):
    "Convert path relative to the location of the TEVS programs"
    return os.path.join(os.path.expanduser("~/tevs/tevs"), *path)

def run(*args):
    return subprocess.Popen(args, cwd=tevspath())

def run_count(cfg):
    main = tevspath("democountlauncher.sh")
    run("/usr/bin/gnome-terminal", "-x", main, "--config", cfg)

def run_display(cfg):
    show = tevspath("show_ballots.py")
    run(show, "--config", cfg)

class App(object):
    def __init__(self):
        self.root = gtk.Window(gtk.WINDOW_TOPLEVEL)
        self.root.set_title("TEVS Demo")

        #these let our window close when someone hits the close button
        self.root.connect("delete_event", self.delete)
        self.root.connect("destroy", self.destroy)

        #create an infobox to display long messages
        self.info = InfoBox()
        self.info.show(introduction)

        #create button bars for each kind of sample image we have
        hart300 = BallotKind(self.info, "Hart Images, 300 dpi", "hart300.cfg")
        hart150 = BallotKind(self.info, "Hart Images, 150 dpi", "hart150.cfg")
        seq300 = BallotKind(self.info, "Sequoia Images, 300 dpi", "seq300.cfg")
        seq150 = BallotKind(self.info, "Sequoia Images, 150 dpi", "seq150.cfg")

        #we just stack all our GUI elements vertically
        con = gtk.VBox()
        con.pack_start(hart300.frame, expand=False)
        con.pack_start(hart150.frame, expand=False)
        con.pack_start(seq300.frame, expand=False)
        con.pack_start(seq150.frame, expand=False)
        con.pack_start(self.info.frame, expand=True)
        self.root.add(con)

        self.root.set_geometry_hints(
            min_width=400, 
            min_height=500,
        )
        self.root.show_all()

    def delete(self, widget, event, data=None):
        return False

    def destroy(self, widget, data=None):
        gtk.main_quit()

class InfoBox(object):
    def __init__(self):
        #create a text area with scrollbars to display long messages
        sw = gtk.ScrolledWindow()
        sw.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)

        self.buffer = gtk.TextBuffer()
        self.text_view = gtk.TextView(self.buffer)
        self.text_view.set_wrap_mode(gtk.WRAP_WORD)

        self.text_view.set_border_width(10)
        sw.add(self.text_view)
        self.frame = sw

    def show(self, text):
        self.buffer.set_text(text)

class BallotKind(object):
    def __init__(self, info, label, cfg_file):
        self.info = info
        self.cfg_file = cfg_file

        #create all the buttons
        count = gtk.Button("Count votes")
        count.connect("clicked", self.count, None)
        count.set_tooltip_text("Process ballots to locate votes, then show summary of votes")

        display = gtk.Button("Display with vote overlay")
        display.connect("clicked", self.display, None)
        display.set_tooltip_text("Display processed ballots with TEVS' vote decisions")
        display.set_sensitive(False) #TODO check if it happened before
        self.display_button = display #we save so we can ungray it later

        #group buttons together horizontally
        group = gtk.HBox()
        for b in (count, display):
            group.pack_start(b)

        #create a frame with the given label
        frame = gtk.Frame()
        frame.set_label(label)
        frame.set_shadow_type(1)
        frame.set_border_width(10)
        frame.add(group)
        self.frame = frame

    def count(self, button, data):
        run_count(self.cfg_file)
        self.info.show(count_message)
        self.display_button.set_sensitive(True)

    def display(self, button, data):
        run_display(self.cfg_file)
        self.info.show(display_message)

def main():
    App() #build our application
    gtk.main() #let gtk take over

if __name__ == '__main__':
    main()
