#!/usr/bin/env python
# TEVS is ballot counting and viewing software.
# Copyright 2008 by Mitch Trachtenberg
# TEVS is licensed under the terms 
# of version 3 of the GNU General Public License.
# When running TEVS, Help-->License 
# will show the text of this license.  The text
# is also in the accompanying file HelpMessages.py.
# Mitch Trachtenberg / PO Box 1352 / Trinidad, CA 95570
# mjtrac@gmail.com

# show_ballots.py is the graphical user interface for viewing results
# Search "version" below for version number.

# 1) get zoom info from slider to resize drawing areas
# 2) remove start/end/now and replace with image>
import os
import pdb
import site; site.addsitedir(os.path.expanduser("~/tevs"))
import const
import config
import exceptions
import getopt
import logging
import pygtk
pygtk.require('2.0')
import gobject
import gtk
import subprocess
import time
from PIL import Image, ImageDraw, ImageFont
from BBUtil import *
import util
#import copy
import fnmatch
import glob
import pickle
import shelve
import string
import sys
import time
import pango
import db

# globals
# unprocessed images are in ~/unproc
# processed images are moved to ~/proc
# per ballot results are written to ~/results/<nnn>/<ballotname>.txt
# likely votes are written to ~/results/votes.csv
# borderline votes are written to ~/results/border.csv

# file naming convention: seven digits followed by .jpg
# file abcdef.jpg will start in ~/unproc/abcd/abcdefg.jpg
# after processing, it will be moved to ~/proc/abcd/abcdefg.jpg
# results will be in ~/result/abcd/abcdef.jpg
# directories abcd are created as needed

# The program keeps track of the highest processed file 
# by reading a seven digit number in ~/processed.txt

# Each call to display the next file checks the contents of ~/processed.txt,
# and attempts to open the file only if its number is below 
# the number tracked in processed.txt, otherwise writing a status message
# and sleeping for five seconds.

# As an image is opened, its corresponding results file is opened and 
# processed.  The results file indicates the location of each oval and
# the text of the choice.  Ovals darkened enough to count as votes are to
# have a box drawn around them, and the choice text printed beside them.

# Depending on the current mode, the program will single step forward
# or backward between processed files, or continually advance after a 
# specified delay.  The mode is set via buttons NEXT, PREV, and CONTINUOUS.
# The delay is set by a spinbutton with range 1-10, representing seconds of
# delay.




# The read file(s) are displayed in side-by-side scrolled windows contained
# in a paned window.  The display is overlaid with boxes around vote ops
# whose results indicate the presence of a vote.

version = "20110911"
debug = False
fileextension = ".jpg"
window = None
gc = None
pixelwidth = 1275. # set this from first template
pixelheight = 1648.# set this from first template
VisualDashCodeDict = {}
DashCodeDict = {}
s2 = None
text_size = "medium"
line_width = 2
code = """
def testFunc(filenum,filename):
   retval = True
   try:
       datafile = open(filename)
   except Exception, e:
       print e
       retval = False
       return retval
   for line in datafile.readlines():
     barcode = line.split(",")[1]
     if barcode.find("1000039")>-1:
       retval = False
       break
   datafile.close()
   print retval
   return retval
"""
def get_args():
    """Get command line arguments"""
    try:
        opts, args = getopt.getopt(sys.argv[1:],
                                    "tdc:",
                                    ["templates",
                                     "debug",
                                     "config="
                                    ]
                                   ) 
    except getopt.GetoptError:
        sys.stderr.write(
            "usage: %s -tdc --templates --debug --config=file" % sys.argv[0]
        )
        sys.exit(2)
    templates_only = False
    debug = False
    config = "tevs.cfg"
    for opt, arg in opts:
        if opt in ("-t", "--templates"):
            templates_only = True
        if opt in ("-d", "--debug"):
            debug = True
        if opt in ("-c", "--config"):
            config = arg

    const.templates_only = templates_only
    const.debug = debug
    return config


def import_code(code):
    import imp
    module = imp.new_module("bbfilters")
    exec code in module.__dict__
    return module

#m = import_code(code)
#m.testFunc(2,"yabba")

def beep():
    audio = file('/dev/audio', 'wb')
    count=0
    while count<25:
        blip=chr(63)+chr(63)+chr(63)+chr(63)
        audio.write(blip)
        blip=chr(0)+chr(0)+chr(0)+chr(0)
        audio.write(blip)
        count=count+1
    audio.close()





def timeout_func(app,spinner):
    #print "In timeout",app,spinner
    app.next_cb(None,None)
    vai = app.spinbutton.get_value_as_int()
    app.timeout = gobject.timeout_add(vai*1000,timeout_func,app,app.spinbutton)
    return False

INDEX_CONTEST = 3
INDEX_CHOICE = 4
INDEX_XCOORD = 22
INDEX_YCOORD = 23
INDEX_INTENSITY = 7
INDEX_WAS_VOTED = 26
INDEX_AMBIGUOUS = 27

class Vote(object):
    def __init__(self,str):
        # split the str into fields, and set values based on field contents
        try:
            fields = str.split(",")
            self.contest = fields[INDEX_CONTEST]
            self.choice = fields[INDEX_CHOICE]
            self.xcoord = int(float(fields[INDEX_XCOORD]))
            self.ycoord = int(float(fields[INDEX_YCOORD]))
            self.intensity = int(float(fields[INDEX_INTENSITY]))
            self.was_voted = fields[INDEX_WAS_VOTED]=="True"
            self.ambiguous = fields[INDEX_AMBIGUOUS]=="True"
        except Exception,e:
            print Exception,e
            print fields
    def xcoord(self):
        return self._xcoord

    def ycoord(self):
        return self._ycoord

class DBVote(Vote):
    def __init__(self):
        # split the str into fields, and set values based on field contents
        pass

    def xcoord(self):
        return self._xcoord

    def ycoord(self):
        return self._ycoord

class BallotVotes(object):
    def __init__(self,filename,imagenumber):
        if const.use_db:
            # query the database for the voteops matching file number
            dbfileroot = const.root+"/unproc"
            dbfilename = "%s/%03d/%06d.jpg" % (
                dbfileroot,imagenumber/1000,imagenumber)
            #print dbfilename
            # perform query

            results = App.dbc.query("select contest_text,choice_text,adjusted_x,adjusted_y,red_mean_intensity, was_voted, suspicious, filename from voteops join ballots on voteops.ballot_id = ballots.ballot_id where filename like '%s'" % (dbfilename,) )
            # unpack results
            #INDEX_CONTEST = 3
            #INDEX_CHOICE = 4
            #INDEX_XCOORD = 22
            #INDEX_YCOORD = 23
            #INDEX_INTENSITY = 7
            #INDEX_WAS_VOTED = 26
            #INDEX_AMBIGUOUS = 27
            self.votelist = []

            if results is not None and len(results)>0:
                for fields in results:
                    v = DBVote()
                    v.contest = fields[0]
                    v.choice = fields[1]
                    v.xcoord = int(float(fields[2]))
                    v.ycoord = int(float(fields[3]))
                    v.intensity = int(float(fields[4]))
                    v.was_voted = fields[5]
                    v.ambiguous = fields[6]
                    v.filename = fields[7]
                    self.votelist.append(v)    

        else:
            # open and read the data file, line by line

            imagenumberstr = "%06d." % imagenumber
            datafilename = const.resultsformatstring % (imagenumber/1000,imagenumber)
            df = None
            try:
                df = open(datafilename,"r")
            except:
                #print "Could not open",datafilename, "trying one lower"
                try:
                    datafilename = const.resultsformatstring % ((imagenumber-1)/1000,imagenumber-1)
                    df = open(datafilename,"r")
                except:
                    print "Could not open",datafilename,"either"
            self.votelist = []
            for line in df.readlines():
                if (line.find(imagenumberstr)>-1):
                    self.votelist.append(Vote(line))
            df.close()


    def paint(self,drawable,gc,markup,xscalefactor,yscalefactor,imagedpi):
        for v in self.votelist:
            scaledx = int(round(v.xcoord*xscalefactor))
            scaledy = int(round(v.ycoord*yscalefactor))
            oval_height = int(const.target_height_inches * imagedpi)
            oval_width = int(const.target_width_inches * imagedpi)
            scaledx += int(round(const.hotspot_x_offset_inches * imagedpi * xscalefactor))
            scaledy += int(round(const.hotspot_y_offset_inches * imagedpi * yscalefactor))

            #oval_height = ((5.*imagedpi)/32.)
            #oval_width = ((5.*imagedpi)/16.)
            box_height = int(round(oval_height * yscalefactor))
            box_width = int(round(oval_width * xscalefactor))
            box_height += 1
            box_width += 1
            cmap = drawable.get_colormap()
            if v.was_voted:
                gc.set_foreground(App.red)
            else:
                gc.set_foreground(App.green)
            if v.ambiguous:
                gc.set_foreground(App.purple)
            drawable.draw_rectangle(gc,False,scaledx,scaledy,box_width,box_height)
            if not App.show_vote_overlay:
                continue
            bg_markup_color="white"
            if v.was_voted:
                markup_color="red"
            else:
                markup_color="blue"
            if v.ambiguous:
                markup_color="yellow"
                bg_markup_color="black"

            if App.show_choice_overlay:
                choicetext = v.choice.replace("dquot",'"').replace("squot","'")[:25]
            else:
                choicetext = ""
            if App.show_contest_overlay:
                contesttext = v.contest.replace("dquot",'"').replace("squot","'")[:25]
            else:
                contesttext = ""
            if App.show_choice_overlay and App.show_contest_overlay:
                text = "%s\n%s" % (contesttext,choicetext)
            else:
                text = "%s%s" % (contesttext,choicetext)
            if text.startswith("v"):text=text[1:]
            markup.set_markup(
                """<span size="%s" foreground="%s" background="%s">%s</span>""" % (
                    text_size,markup_color,bg_markup_color,text
                    )
                )
            # draw markup at lower right of vote oval, offset by 5 pix 
            drawable.draw_layout(gc,
                               scaledx+box_width+5,
                               scaledy+5,
                               markup)

class BrowsingException(exceptions.Exception):
    def __init__(self,args = None):
        self.args = args
    def __str__(self):
        return repr(self.args)

def create_arrow_button(arrow_type, shadow_type):
   button = gtk.Button();
   arrow = gtk.Arrow(arrow_type, shadow_type);
   button.add(arrow)
   button.show()
   arrow.show()
   return button

def help_overview_cb( b):
        print 'Help overview'

def destroy_cb(cb, data):
    gtk.main_quit()
    sys.exit(0)

def quit_cb(cb):
    gtk.main_quit()
    sys.exit(0)

def all_files_in_folder(root,
                        patterns="*",
                        single_level=False, 
                        yield_folders=False):
    """
    From ORA Python Cookbook. 
    This generates all filenames matching patterns in a specified list
    under a specified root directory.
    """
    patterns = patterns.split(';')
    for path, subdirs, files in os.walk(root):
        if yield_folders:
            files.extend(subdirs)
        files.sort()
        for name in files:
            for pattern in patterns:
                if fnmatch.fnmatch(name,pattern):
                    yield os.path.join(path,name)
                    break
        if single_level:
            break


class App():

    # votescsv is the name of a file that receives one line for each vote,
    # in the comma separated field format 
    # imagename, dashcode, contest, choice, "Debug", xloc, yloc, intensity
    # intensity is on a scale of 0 (black) to 255 (white)
    votescsv = "votes.csv"
    nonvotescsv = "nonvotes.csv"
    # countedvotescsv is a copy of the contents of votescsv, 
    # created once a complete count has been performed; 
    # countedvotescsv can then serve as input to search functions
    countedvotescsv = "countedvotes.csv"
    # precinctcsv is the name of a file that receives one line for
    # each dash code encountered, in the comma separated field format
    # precinct, dashcode
    filename_extension = ".jpg"




    pct_left_meter = None
    current_after = None # the currently registered "after" function
    stopped = True
    display = None
    displaywidth = 0
    displayheight = 0
                                   # with precincts instead of dash codes
    current_folder = "."
    skip_count = 1
    current_filename = None
    on_deck_filename = None


    start_labelentry = None # the widget with starting filenumber, to unpack
    end_labelentry = None # the widget with ending filenumber, to unpack

    all_images = []
    last_filenames = []
    last_votes = []
    last_ballots = []
    show_vote_overlay = True
    show_contest_overlay = True
    show_choice_overlay = True
    red = None
    green = None
    blue = None
    def displayNextFile(self,
			filename
			):
	    """
	    For now, the only processing we do is count the votes
	    """
	    return self.b.votes(self.templates)

    def count_all_cb(self,ta):
        self.count_all = ta.get_active()
	self.entry_start.set_sensitive(not self.count_all)
	self.entry_end.set_sensitive(not self.count_all)
        self.statusbar.push(self.contextid,
                            "Count all set to %s" % (self.count_all,))
	self.set_ballot_folder(None)

    def show_vote_cb(self,ta):
        App.show_vote_overlay = not App.show_vote_overlay
	self.expose_cb(self.i1,None,(1,None))
	self.expose_cb(self.i2,None,(2,None))

    def show_contest_cb(self,ta):
        App.show_contest_overlay = not App.show_contest_overlay
	self.expose_cb(self.i1,None,(1,None))
	self.expose_cb(self.i2,None,(2,None))

    def show_choice_cb(self,ta):
        App.show_choice_overlay = not App.show_choice_overlay
	self.expose_cb(self.i1,None,(1,None))
	self.expose_cb(self.i2,None,(2,None))

    def zoom_update_cb( self, adj, hscale ):
        v = adj.get_adjustment().get_value()
        #print v
        (w,h) = self.leftimage.size
        self.i1.set_size_request(int(w*v),int(h*v))
        self.i1.width = int(w*v)
        self.i1.height = int(h*v)
        try:
            (w,h) = self.rightimage.size
            self.i2.set_size_request(int(w*v),int(h*v))
            self.i2.width = int(w*v)
            self.i2.height = int(h*v)
        except:
            pass

    def contbutton_cb(self,button,data):
        # update numbers forward by 2, reload files, expose

        if button.get_active():
            self.timeout = gobject.timeout_add(2000,
                                               timeout_func,
                                               self,
                                               self.spinbutton)
        else:
            try:
                gobject.source_remove(self.timeout)
                self.timeout = None
            except TypeError,e:
                print e
                pass
	self.expose_cb(self.i1,None,(1,None))
	self.expose_cb(self.i2,None,(2,None))

    def go_cb(self,button,data):
        # the call to "increment" just retrieves the text from the nowentry,
        # loads the new file numbers, and triggers exposures

        self.increment_file_number(0)
	self.expose_cb(self.i1,None,(1,None))
	self.expose_cb(self.i2,None,(2,None))


    def next_cb(self,button,data):
        # update numbers forward by 2, reload files, expose
        self.increment_file_number(const.num_pages)
	self.expose_cb(self.i1,None,(1,None))
	self.expose_cb(self.i2,None,(2,None))


    def prev_cb(self,button,data):
        # update numbers backwards by 2, reload files, expose
        self.increment_file_number(0-const.num_pages)
	self.expose_cb(self.i1,None,(1,None))
	self.expose_cb(self.i2,None,(2,None))

    def increment_file_number(self,inc):
        skip = True
        while(skip):
            try:
                self.leftnumber = int(self.nowentry.get_text())
                self.rightnumber = self.leftnumber + 1
            except Exception, e:
                print "Could not get integer value from entered text."
                print e
            try:
                self.leftfilename = const.procformatstring % ((self.leftnumber+inc)/1000,self.leftnumber+inc)
                self.rightfilename = const.procformatstring % ((self.rightnumber+inc)/1000,self.rightnumber+inc)
                self.leftimage = Image.open(self.leftfilename)
                self.rightimage =Image.open(self.rightfilename)

                self.leftnumber += inc
                self.rightnumber += inc
            except:
                beep()

            self.leftfilename = const.procformatstring % ((self.leftnumber+inc)/1000,self.leftnumber+inc)
            self.rightfilename = const.procformatstring % ((self.rightnumber+inc)/1000,self.rightnumber+inc)
            self.leftdatafilename = const.resultsformatstring % ((self.leftnumber+inc)/1000,self.leftnumber+inc)
            self.rightdatafilename = const.resultsformatstring % ((self.rightnumber+inc)/1000,self.rightnumber+inc)

            # if a filtering function has been set, apply it
            # to each new file number;
            # the filtering function should check the file
            # and return True if the file is in the category
            # being checked, else False            
            try:
                skip = False
                skip = m.testFunc(self.leftnumber,self.leftdatafilename)
                #skip = m.testFunc(self.leftnumber,self.rightdatafilename)
                self.nowentry.set_text("%06d" % self.leftnumber)
                while gtk.events_pending():
                    gtk.main_iteration(False)
                if skip: continue
            except:
                skip = False
            
            self.leftbv = BallotVotes(self.leftdatafilename,self.leftnumber)
            self.rightbv = BallotVotes(self.rightdatafilename,self.rightnumber)
            self.nowentry.set_text("%06d" % self.leftnumber)


    def expose_cb(self, da, event, data2):
        global gc
        i = data2[0]
        markup = self.leftmarkup
        bv = self.leftbv
        image = self.leftimage
        #xscalefactor = 0.25
        #yscalefactor = 0.2
        if i == 1:
            bv = self.leftbv
            markup = self.leftmarkup
            image = self.leftimage
        elif i==2:
            bv = self.rightbv
            markup = self.rightmarkup
            image = self.rightimage
        if gc is None:
            cmap = da.window.get_colormap()
            App.green = cmap.alloc_color("green")
            App.red = cmap.alloc_color("red")
            App.blue = cmap.alloc_color("blue")
            App.purple = cmap.alloc_color("purple")
            gc = da.window.new_gc(foreground=App.green)
            
            gc.set_line_attributes(line_width,
                                   gtk.gdk.LINE_SOLID,
                                   gtk.gdk.CAP_BUTT,
                                   gtk.gdk.JOIN_BEVEL)
        if i==1 and self.leftmarkup is None:
            markup = da.create_pango_layout("a")
            self.leftmarkup = markup
        elif i==2 and self.rightmarkup is None:
            markup = da.create_pango_layout("a")
            self.rightmarkup = markup

        try:
            w = da.width
            h = da.height
            if image is None:
                pass
            else:
                imagewidth, imageheight = image.size
                imagedpi = int(round(image.size[0]/const.ballot_width_inches))
                xscalefactor = float(w)/imagewidth
                yscalefactor = float(h)/imageheight
                image = image.resize((w,h)).convert("RGB")
                imagestr = image.tostring()
                da.window.draw_rgb_image(
                    gc, 
                    0, 0, 
                    w, h, 
                    gtk.gdk.RGB_DITHER_NONE, 
                    imagestr, 
                    w*3
                    )
                bv.paint(da.window,gc,markup,xscalefactor,yscalefactor,imagedpi)
        except Exception, e:
            print e
		    
        return False

    def notebook_expose_cb(self, da, event, data2):
	    global gc
	    global markup
            print "Notebook exposure",da
	    try:
		    da.b.gtkdisplay(gc, 
				      markup,
				      da.window, 
				      da.width, 
				      da.height,
				      show_votes = True)
	    except Exception, e:
		    print Exception, e
		    
	    return False

    def notebook_configure_cb(self, da, event):
	da.width = event.width
	da.height = event.height

    def motion_notify_cb(self, da, event):
        pass

    def button_press_cb1(self, da, event):
        self.button_press_cb(da,event,1)
    def button_press_cb2(self, da, event):
        self.button_press_cb(da,event,2)

    def button_press_cb(self, da, event,da_number):
        width = da.width
        height = da.height
        try:
            first_image = int(self.nowentry.get_text())
            second_image = first_image+1
        except Exception, e:
            print e
        if da_number == 1:
            image_number = first_image
        else:
            image_number = second_image
        pct_of_width = 100.*float(event.x)/width
        pct_of_height = 100*float(event.y)/height
        print "Image: %d; pct_of_width %d%%; pct_of_height %d%%, button %d" % (
            image_number,
            pct_of_width,
            pct_of_height,
            event.button)

    def key_press_cb(self, window, event):
        #print "Key",self,event
        #print event.string, self.leftnumber, self.rightnumber
        pass

    def configure_cb(self, da, event, data):
        # from pygtk tutorial
        x,y,width,height = da.get_allocation()
        #print x, y, width, height
        self.leftpixmap = gtk.gdk.Pixmap(da.window,da.width,da.height) 
	# call expose callback to clean up
	self.expose_cb(da,event,data)

    def create_names(self):
        """
        Creates a list of filenames from a number range,
        such that the filename list can be used in place
        of the filename list generated by walking a directory tree.
        """
	start_text = self.entry_start.get_text()
	end_text = self.entry_end.get_text()
	#print "Create names: start_text, end_text",start_text,end_text
        for n in range(string.atoi(end_text),
                       string.atoi(start_text)-1,-1
                       ):
            n10000s = int(n/10000)
            n100s = int(n/100) % 100
            n1s = n%100
            App.all_images.append("%s/%02d/%02d/%06d%s"
                                  % (self.number_dir,
                                     n10000s,
                                     n100s,
                                     n,
                                     App.filename_extension))
        nf = self.next_filename()
        App.on_deck_filename = nf
        return nf


    def specify_number_dir(self,this_dir):
        self.number_dir = this_dir
	self.statusbar.push(self.contextid,"Ballot folder base set to '%s'"% (this_dir,))

	self.base_dir_label.set_text("Ballot root: %s"%(this_dir,))

    def create_filelist_from_dir(self,this_dir):
        """
        Creates a list of all image files under a specified directory,
        pops the first entry in the list into App.on_deck_filename,
        and sets the file listing as App.all_images
        """
        App.current_folder = this_dir
        #App.start_labelentry["state"] = "disabled"
        #App.end_labelentry["state"] = "disabled"
	# modified 7/23/2009 mjt for Ann Arbor, get only fronts for this pass
        App.all_images = all_files_in_folder(
                this_dir,
                patterns="*"+App.filename_extension)
        try:
            App.on_deck_filename = App.all_images.next()
        except StopIteration:
            App.all_images = []
        return 
            
    def process_external_file_list(self,list_file):
        print "Processing files from external list",list_file
        # put files in all_images, start counting
        votefile = open(list_file,"r")
        lastl = None
        App.all_images = []
        for l in votefile.xreadlines():
            if l != lastl:
                App.all_images.append(l[:-1])
            lastl = l
        votefile.close()
        # reverses in place, so that first filename is first to pop
        App.all_images.reverse()
        try:
            App.on_deck_filename = App.all_images.pop()
            self.go_cb()
        except IndexError:
            showinfo("No matches.","No matches.",App.root)

    def files_not_in_sequence(self):
        # populate list from output of a script like findmissing
        # operating on countedvotes.csv
        pass

    def files_for_precinct_cb(self,data):
        # determine dash code corresponding to precinct
        # scan countedvotes.csv to find files with that dash code
        # put files in all_images, start counting
        # solicit precinct from user
        dc_matches = []
        precinct_string = askstring("Precinct",
"""Enter a precinct or part of a precinct
(for example, 1CS1 or 1CS)""","Enter precinct:",App.root)
        print "Precinct",precinct_string
        precinct_string = precinct_string.replace("-","").strip(" \n\t").upper()
        # look up dash code(s) corresponding to precinct
        if os.path.exists(App.precinctcsv):
            dcfile = open(App.precinctcsv,"r")
            for dcline in dcfile.readlines():
                (pr,dc) = dcline[:-1].split(",")
                pr = pr.replace("-","").strip(" ,\n\t").upper()
                if pr.startswith(precinct_string):
                    dc_matches.append(dc[1:].strip(" \n"))
            dcfile.close()

        # search through countedvotes.csv for lines with the dash code(s)
        lastfield1 = None
        App.all_images = []
        if os.path.exists(App.countedvotescsv):
            try:
                ov = open(precinct_string,"w")
            except:
                ov = None
            try:
                for dc in dc_matches:
                    cv = open(App.countedvotescsv)
                    for line in cv:
                        try:
                            field1 = line.split(",")[0]
                            if (line.find(dc) > -1) and (field1 != lastfield1):
                                try:
                                    ov.write(field1)
                                    ov.write("\n")
                                except:
                                    pass
                                App.all_images.append(field1)
                                lastfield1 = field1
                        except:
                            print "Problem:",line
                    cv.close()
            except:
                pass
            try:
                ov.close()
                showinfo("Wrote file %s" % (precinct_string,),
                                      "Wrote files representing precinct %s \nto file named %s.\n\nWill now continue \nby counting these files,\nplacing results into votes.csv" % (precinct_string,precinct_string),App.root)
            except:
                pass
        # reverses in place, so that first filename is first to pop
        App.all_images.reverse()
        try:
            App.on_deck_filename = App.all_images.pop()
            self.go_cb()
        except IndexError:
            showinfo("No matches.","No matches.",App.root)

    def files_from_external_file_list_cb(self,extra):
        # get filename from file selector
        fsd = gtk.FileChooserDialog("Yabba",
				    buttons=(gtk.STOCK_CANCEL, 
					     gtk.RESPONSE_REJECT,
					     gtk.STOCK_OK, 
					     gtk.RESPONSE_ACCEPT))
        retval = fsd.run()
	print retval,
	fn = fsd.get_filename()
	print fn
	fsd.destroy()
	self.process_external_file_list(fn)

    def files_with_nonvote_matching_intensity(self,start=216,end=230):
        # pass list to all_images
        lastfield1 = None
        App.all_images = []
        try:
            cv = open(App.nonvotescsv)
            for line in cv:
                fields = line.split(",")
                if (int(fields[7][:-1]) <= int(end)) and (fields[0] != lastfield1):
                    App.all_images.append(fields[0])
                    lastfield1 = fields[0]
            cv.close()
        except:
            pass

        # reverses in place, so that first filename is first to pop
        App.all_images.reverse()
        try:
            intensity_title = "intensity_near_threshold"
            ov = open(intensity_title,"w")
            for ol in App.all_images:
                ov.write(ol)
                ov.write("\n")
            showinfo("Wrote file %s" % (intensity_title,),
                                  "Wrote file %s" % (intensity_title,),App.root)
        except:
            pass
        finally: 
            ov.close()

        try:
            App.on_deck_filename = App.all_images.pop()
            self.go_cb()
        except IndexError:
            showinfo("No matches.","No matches.",App.root)

    def files_with_vote_matching_intensity(self,start=206):
        # pass list to all_images
        lastfield1 = None
        App.all_images = []
        try:
            cv = open(App.countedvotescsv)
            for line in cv:
                #pdb.set_trace()
                fields = line.split(",")
                if (int(fields[7][:-1]) >= int(start)) and (fields[0] != lastfield1):
                    App.all_images.append(fields[0])
                    lastfield1 = fields[0]
            cv.close()
        except:
            pass

        # reverses in place, so that first filename is first to pop
        App.all_images.reverse()
        try:
            intensity_title = "intensity_just_below_threshold"
            ov = open(intensity_title,"w")
            for ol in App.all_images:
                ov.write(ol)
                ov.write("\n")
            showinfo("Wrote file %s" % (intensity_title,),
                                  "Wrote file %s" % (intensity_title,),App.root)
        except:
            pass
        finally: 
            ov.close()
        try:
            App.on_deck_filename = App.all_images.pop()
            self.go_cb()
        except IndexError:
            showinfo("No matches.","No matches.",App.root)

    def files_with_matching_string(self,matchstr):
        # pass list to all_images
        lastfield1 = None
        App.all_images = []
        try:
            cv = open(App.countedvotescsv)
            for line in cv:
                #pdb.set_trace()
                fields = line.split(",")
                if line.find(":OV")>=0:
                    App.all_images.append(fields[0])
                    lastfield1 = fields[0]
            cv.close()
        except:
            pass

        # reverses in place, so that first filename is first to pop
        App.all_images.reverse()
        try:
            ov_title = "overvoted"
            ov = open(ov_title,"w")
            for ol in App.all_images:
                ov.write(ol)
                ov.write("\n")
            showinfo("Wrote file %s" % (ov_title,),
                                  "Wrote file %s" % (ov_title,),App.root)
        except:
            pass
        finally: 
            ov.close()
        try:
            App.on_deck_filename = App.all_images.pop()
            self.go_cb()
        except IndexError:
            showinfo("No matches.","No matches.",App.root)

    def files_with_overvotes(self):
        self.files_with_matching_string(":OV")


    def select_file_to_merge(self,data):
        """
        Pick the file containing an additional pickled dictionary
        to be merged with that currently set.
        """
	print self
	print data
        fcd = gtk.FileChooserDialog(title = "Merge file",
		action = gtk.FILE_CHOOSER_ACTION_OPEN,
		buttons=(gtk.STOCK_CANCEL, 
			 gtk.RESPONSE_REJECT,
			 gtk.STOCK_OK, 
			 gtk.RESPONSE_ACCEPT))

	retval = fcd.run()
	if retval == gtk.RESPONSE_ACCEPT:
		f = fcd.get_filename()
		self.merge_count(f)
	fcd.destroy()
        #dsd = Tix.FileSelectDialog(root,command=self.merge_count)
        #dsd.popup()

    def select_dir(self):
        """
        Pick the directory under which your files are located,
        then call create_filelist_from_dir to build a list 
        of image files under that directory.
        """
	pass

    def set_ballot_folder(self,data):
        """
        Pick the directory under which a standard numbered
        filetree is located.  Standard numbered filetrees
        have directories named 00-99 (nn), which in turn contain
        subdirectories named 00-99 (mm) or, at the leaves, files
        named nnmm00.jpg through nnmm99.jpg
        """
	print data
        fcd = gtk.FileChooserDialog(
		title = "Select ballot folder",
		action = gtk.FILE_CHOOSER_ACTION_SELECT_FOLDER,
		buttons=(gtk.STOCK_CANCEL, 
			 gtk.RESPONSE_REJECT,
			 gtk.STOCK_OK, 
			 gtk.RESPONSE_ACCEPT))

	retval = fcd.run()
	if retval == gtk.RESPONSE_ACCEPT:
		folder = fcd.get_current_folder()
		if self.count_all:
			self.create_filelist_from_dir(folder)
		self.specify_number_dir(folder)
	fcd.destroy()

    def outputTheVoteDictionary(self,label="Report",pdf=True,precincts=False):
        """
        Takes the vote dictionary, converts dash codes to precincts
        if possible, sorts once by classifier and once by contest, and, 
        for each sorting, creates PDF using ElectionReport,
        and returns text suitable for output to txt file.
        """
        master_outstr_list = []
        outstr_list = []
        # first, get all different k[0]'s (classifiers)
        # and k[1]'s (contests)
        classifier_dict = {}
        contest_dict = {}

        # App.precinctcsv, if found,
        # has a map from precincts to dash codes
        # and we can build a version of the vote dictionary
        # using precinct names instead of dash codes,
        # first, load csv into a _dict, with the
        # dash codes as keys and the precincts as values;
        # second, create a votebyprecinct_dict to store modified entries,
        # then, for every key in the vote_dictionary,
        # create a new key in votebyprecint_dict that replaces
        # the dashcode element of the key with the
        # value from looking that element up in dc2precinct_dict
        # and finally store the value from vote_dict in votebyprecinct_dict
        dc2precinct_dict = {}
        if os.path.exists(App.precinctcsv) and precincts==True:
            dcfile = open(App.precinctcsv,"r")
            for dcline in dcfile.readlines():
                (pr,dc) = dcline[:-1].split(",")
                if dc.startswith("0"):
                    dc = dc[1:]
                dc2precinct_dict[dc] = pr 
        App.votebyprecinct_dictionary = {}
        for k in App.vote_dictionary.keys():
            try:
                dc2precinct_dict[k[0]]
                newkey = (dc2precinct_dict[k[0]],k[1],k[2])
                try:
                    App.votebyprecinct_dictionary[newkey] += App.vote_dictionary[k]
                except:
                    App.votebyprecinct_dictionary[newkey] = App.vote_dictionary[k]
            except:
                #no such dashcode entry in precinct dictionary, 
                #just use dashcode rather than mapping to precinct
                try:
                    App.votebyprecinct_dictionary[k] += App.vote_dictionary[k]
                except:
                    App.votebyprecinct_dictionary[k] = App.vote_dictionary[k]

        for k in App.votebyprecinct_dictionary.keys():
                classifier_dict[k[0]] = 1
                contest_dict[k[1]] = 1
        classifier_list = classifier_dict.keys()
        classifier_list.sort()
        contest_list = contest_dict.keys()
        contest_list.sort()
        #if pdf: 
        #    try:
        #        er = ElectionReport.ElectionReport()
        #    except:
        #        er = None

        percent_dict = {}
        keylist = App.votebyprecinct_dictionary.keys()

        # sort keylist by precinct, contest, then choice
        # (or: contest, precinct, choice)

        # First, show results by precinct
        keylist.sort(lambda x,y: (
                cmp(x[1],y[1]) or cmp(x[0],y[0]) or cmp(x[2],y[2])
                ))
        try:
            k0 = keylist[0][0]
            k1 = keylist[0][1]
            k2 = keylist[0][2]
        except:
            return "No votes.\n"
        sum = 0
        for k in keylist:
            # if the precinct has changed, output the stored counts
            if k[0] != k0:
                # calculate percentages for the prior k1 contest
                # by summing all saved vote counts and dividing
                # individual vote counts by the sum
                outstr_list = []
                sum = 0
                pdklist = percent_dict.keys()
                # until the precinct changes, keep summing
                for pdk in pdklist:
                    # don't include :OVERVOTED in percentages
                    if pdk[2].find(":OV") == -1:
                        sum += percent_dict[pdk]
                for pdk in pdklist:
                    try:
                        percent_dict[pdk] = (percent_dict[pdk],
                                             (percent_dict[pdk]*100)/float(sum)
                                             )
                    except:
                        percent_dict[pdk] = (percent_dict[pdk],0)
                for pdk in pdklist:
                    outstr_list.append( "%10s, %25s, %25s, %05s, %06.2f" % ( 
                        pdk[0],
                        pdk[1], 
                        pdk[2], 
                        percent_dict[pdk][0],
                        percent_dict[pdk][1]))
                k0 = k[0]
                percent_dict = {}
                master_outstr_list.extend(outstr_list)
            percent_dict[k] = App.votebyprecinct_dictionary[k]

        # sort keylist by precinct, contest, then choice
        # (or: contest, precinct, choice)

        # Then, show results by contest
        keylist.sort(lambda x,y: (
                cmp(x[0],y[0]) or cmp(x[1],y[1]) or cmp(x[2],y[2])
                ))
        k0 = keylist[0][0]
        k1 = keylist[0][1]
        k2 = keylist[0][2]

        for k in keylist:
            # if the contest has changed, process the stored vote counts
            if k[1] != k1:
                # calculate percentages for the prior k1 contest
                # by summing all saved vote counts and dividing
                # individual vote counts by the sum
                outstr_list = []
                sum = 0
                pdklist = percent_dict.keys()
                # until the precinct changes, keep summing
                for pdk in pdklist:
                    # don't include :OVERVOTED in percentages
                    if pdk[2].find(":OV") == -1:
                        sum += percent_dict[pdk]
                for pdk in pdklist:
                    try:
                        percent_dict[pdk] = (percent_dict[pdk],
                                             (percent_dict[pdk]*100)/float(sum)
                                             )
                    except:
                        percent_dict[pdk] = (percent_dict[pdk],0)
                for pdk in pdklist:
                    outstr_list.append( "%10s, %25s, %25s, %05s, %06.2f" % ( 
                        pdk[0],
                        pdk[1], 
                        pdk[2], 
                        percent_dict[pdk][0],
                        percent_dict[pdk][1]))
                k1 = k[1]
                percent_dict = {}
                percent_dict[k] = App.votebyprecinct_dictionary[k]
                master_outstr_list.extend(outstr_list)
            percent_dict[k] = App.votebyprecinct_dictionary[k]

        #Last, show totals per choice, ordered by contest
        choice_dict = {}
        keylist.sort(lambda x,y: cmp(x[1],y[1]) or cmp(x[2],y[2]))
        k1 = keylist[0][1]
        k2 = keylist[0][2]
        contesttotal = 0

        for k in keylist:
            if k[1] != k1:
                # output and reset choice_dict for different contest
                outstr_list.append("\n**** %s *****" % (k1,))
                percentvote = 0
                for ck in choice_dict.keys():
                    try:
                        percentvote = (choice_dict[ck] * 100.0)/contesttotal
                    except:
                        percentvote = 0.
                    outstr_list.append(
                        " %25s, %06d, %05.2f" % 
                        (ck,choice_dict[ck],percentvote))
                choice_dict = {}
                k1 = k[1]
                contesttotal = 0
                master_outstr_list.extend(outstr_list)
                outstr_list = []
            # add to total for choice
            thisvote = App.votebyprecinct_dictionary[k]
            # don't include :OVERVOTED in percentages
            if k[2].find(":OV") == -1:
                contesttotal += thisvote
            try:
                choice_dict[k[2]] = choice_dict[k[2]] + thisvote
            except:
                choice_dict[k[2]] = thisvote

        return "\n".join(master_outstr_list)
                
    def enterTheVotesInDictionary(self,votes):
        """
        The votes dictionary is keyed by dashcode, contest, and choice;
        this function takes a string with fields separated by commas
        and records by newlines, skips the first field and uses the next
        three as key components and the final as value.
        """
        # votes is a \n separated string, with each line
        # consisting of a comma separated tuple of:
        # filename, dash_code, contest, choice
        for v in votes.split("\n"):
            try:
                vs = v.split(",")
                if len(vs) < 4:
                    continue
            except:
                continue
            try:
                App.vote_dictionary[(vs[1], vs[2], vs[3])] += 1
            except IndexError:
                showinfo("Error",
                 "Trouble recording votes in dictionary from %s." % (votes,)
                                         ,App.root)
            except:
                App.vote_dictionary[(vs[1], vs[2], vs[3])] = 1

    def enterTheVotesInCSVFile(self,votes,outfile=votescsv):
        """ 
        Write the votes string to file votes.csv
        """
        try:
            csvfile = open(outfile,"a")
            csvfile.write(votes)
            csvfile.close()
        except:
            showinfo("Error",
                                   "Problem writing to votes.csv"
                           ,App.root        )

    def enterTheVotesInExcel(self, votes):
        """
        Write the votes string to an xlwt object that will
        eventually write to votes.xls.
        The object may end up taking a lot of memory, in 
        which case we'll need to look at alternatives.
        """
        # votes is a \n separated string, with each line
        # consisting of a comma separated tuple of:
        # filename, dash_code, contest, choice
        for v in votes.split("\n"):
            vs = v.split(",")
            if len(vs)<4:
                continue
            try:
                self.ws.write(self.rownum,0,vs[0])
                self.ws.write(self.rownum,1,vs[1])
                # todo, extract card type
                self.ws.write(self.rownum,2,vs[1])
                self.ws.write(self.rownum,3,vs[2])
                self.ws.write(self.rownum,4,vs[3])
                self.rownum += 1
            except:
                tkMessageBox.showerror("Problem",
                                       "Problem writing to Excel."
                                      )

    def flag_cb(self,*args):
	    """
	    Output the name of the current file, and the fact it was flagged.
	    """
	    print "FLAGGED",App.current_filename
            try:
                dialog = gtk.Dialog(buttons=(gtk.STOCK_OK,gtk.RESPONSE_ACCEPT))
                notebook = gtk.Notebook()
                notebook.set_size_request(250,420)
                for n in range(3):
                    da = gtk.Image()
                    da.set_size_request(250,400)
                    da.width = 250
                    da.height = 400
                    da.connect("expose_event",self.notebook_expose_cb,None)
                    da.connect("configure_event",self.notebook_configure_cb)
                    try:
                        da.b = App.last_ballots[n]
                    except:
                        pass
                    try:
                        label_label = da.b.filename[-10:-4]
                    except:
                        label_label = "Back %d" % (n+1,)
                    label = gtk.Label(label_label)
                    notebook.append_page(da, label)
                    da.show()
                    label.show()
                dialog.get_children()[0].pack_start(notebook,True,True,0)
                dialog.show()
                notebook.set_show_tabs(True)
                notebook.set_current_page(1)
                notebook.show()
                exitval = dialog.run()    
                dialog.destroy()
            except Exception, e:
                print Exception, e

    def pause_cb(self,*args):
	    """
	    Output the name of the current file, and the fact we have paused.
	    """
	    print "PAUSED at ",App.current_filename
	    App.stopped = True
	    gobject.source_remove(App.current_after)

    def done_cb(self,*args):
        """
        Cancel any registered after function and set stopped True.
        Then set on_deck to None and set list of files to check to None
        """
	gobject.source_remove(App.current_after)
        #App.pct_left_meter.after_cancel(App.current_after)
        App.stopped = True
        ondeck = None
        nf = None
        App.all_images = []
        try:
            f = open("votes.txt","w")
            f.write(self.outputTheVoteDictionary(pdf=True,precincts=True))
            f.close()
            do_modal_dialog("Summary written to votes.txt, \ndetails in votes.csv and nonvotes.csv",App.root)
        except:
		do_modal_dialog("Problem writing to votes.txt",App.root)
     


    def xgo_cb(self,*args):
        """
        Start the count if stopped (stopped) is True. Otherwise, do nothing.
        """
	#print "go_cb"
        if App.stopped:
	    #print "App was stopped, starting."	
            App.stopped = False
	    #print "on_deck_filename",App.on_deck_filename
            try:
                ondeck = App.on_deck_filename
		#print "ondeck",ondeck
                if ondeck is None or ondeck == "None" or len(ondeck)<1:
                    ondeck = self.create_names()
            except: 
                print "In exception, calling create_names()"
                ondeck = self.create_names()
                ondeck = App.on_deck_filename
            App.current_after = gobject.timeout_add(100,self.repeater)
        else:
            pass

    def pause_command(self,*args):
        """
	See pause_cb
        Cancel any registered after function and set stopped (stopped) True.
        """
	gobject.source_remove(App.current_after)
        #App.pct_left_meter.after_cancel(App.current_after)
        App.stopped = True
        try:
            dialog = gtk.Dialog()
            notebook = gtk.Notebook()
            drawingarea = []
            dialog.vbox.pack_start(notebook)
            for n in range(3):
                drawingarea.extend([gtk.DrawingArea()])
                notebook.append_page(drawingarea[-1], "DA %d"%(n+1,))
            exitval = dialog.run()    
            print exitval
        except:
            pass


    def next_filename(self):
        """
        Return the name of the next image file to process, 
        skipping App.skip_count worth of files.  
        App.skip_count can be set to 20 from the menu to give
        a quick 5% count of a directory tree.
        """
        try:
            for x in range(App.skip_count):
                #generators will have next, lists will have pop
                try:
                    nf = App.all_images.next()
                except AttributeError:
                    try:
                        nf = App.all_images.pop()
                    except IndexError:
                        nf = None
			App.all_images = []
                        break
                except StopIteration:
			print "STOP ITERATION"
			nf = None
			App.all_images = []
			break
            return nf
        except Exception, e:
            print e
            return None

    def trigger(self):
        """
        trigger is the function which is registered to run 
        when the appropriate delay has elapsed AND any events
        that were pending have been processed.
        The actual processing is a call to displayNextFile
        """
	global s2
	global gc
	global markup
	global window
        # get the file number to display
        filenum = ""
        # get the results to display
        try:
            # get the scale at which the file should be displayed
	    scale_multiple = self.zoomslider.get_value()
	    window.set_title("Ballot Browser %s" % (filenum,))
	    try:
		    self.label_now2.set_text("...%s" % (App.current_filename[-15:],))
	    except:
		    self.label_now2.set_text(filenum)
		    
	    problemstr = ""
	    try:
                # open the image file
                # open the results file
                # set the image file as the background of sw1
                # draw the results onto sw1
                pass
                if duplex:
                    # open the next image file
                    # open the next results file
                    # set the image file as the background of sw2
                    # draw the results onto sw2
                    pass
	    except Exception, e:
		    print Exception, e
		    problemstr = "Could not display "+filenum
		    raise BrowsingException, problemstr


	except BrowsingException, problemstr:
		print "BrowsingException", problemstr
		
	try:
	    if gc == None:
		cmap = self.i.window.get_colormap()
		gc = self.i.window.new_gc(foreground=cmap.alloc_color("green"))

	    if markup == None:
		    pc = self.i.get_pango_context()
                    markup = pango.Layout(pc)

	    self.b.gtkdisplay(gc, 
			      markup, 
			      self.i.window, 
			      self.i.width, 
			      self.i.height, 
			      show_votes = True)
	except Exception, e:
		print Exception, e
		

        # hold up to five processed filenames for peeking backwards
        try:
            App.last_votes.insert(0,retstr)
        except Exception, data:
            print "Problem inserting into App.last_votes",Exception, data

        if len(App.last_votes)>5:
            App.last_votes = App.last_votes[:-1]

        try:
            App.last_ballots.insert(0,self.b)
        except Exception, data:
            print "Problem inserting into App.last_ballots",Exception, data
        if len(App.last_ballots)>5:
            App.last_ballots = App.last_ballots[:-1]

        App.last_filenames.insert(0,filenum)
        if len(App.last_filenames)>5:
            App.last_filenames = App.last_filenames[:-1]
    
        nf = self.next_filename()
        return False

    def repeater(self):
        """
        repeater is a function that measures elapsed time,
        decrements the slider in the gui, and registers trigger
        as an after_idle func when enough time has elapsed.
        """
        curpct = float(self.pct_left_meter.get_value())
        ds = self.delay_seconds
        if ds < 0.01:
            ds = 0.3
        curpct -= 0.1 
        self.pct_left_meter.set_value(curpct)
        
        if curpct < 0.01:
            # register this processing as an after_idle func,
            # so that we ensure events get processed even if
            # delay has been set to zero
            self.pct_left_meter.set_value(1*ds)
            gobject.idle_add(self.trigger)
        if not App.stopped:
            App.current_after = gobject.timeout_add(
                int(100 * ds),
                self.repeater)
        return False

    def donotdelete(self):
        pass

    #def quitfromdelete(self,e,d,f):
    #    self.quitplease(d)

    def quitplease(self,data):
        """Quit"""
        gtk.main_quit()
        sys.exit(0)
        #if do_modal_dialog("Really quit?",App.root) == gtk.RESPONSE_ACCEPT:
	#	gtk.main_quit()

    def show_help_overview(self):
        """Show help overview"""
        HelpDialog(root,"Ballot Browser Overview",HelpMessages.overview)

    def show_help_quickstart(self):
        """Show help overview"""
        HelpDialog(root,"Ballot Browser Quickstart",HelpMessages.quickstart)

    def show_help_file(self):
        """Show help for file menu"""
        HelpDialog(root,"Ballot Browser File Menu Help",HelpMessages.file)

    def show_help_preferences(self):
        """Show help for preferences menu"""
        HelpDialog(root,"Ballot Browser Preferences Menu Help",HelpMessages.preferences)

    def show_help_lists(self):
        """Show help for lists menu"""
        HelpDialog(root,"Ballot Browser Lists Menu Help",HelpMessages.lists)

    def show_help_customization(self):
        """Show help customization"""
        HelpDialog(root,"Ballot Browser Customization",HelpMessages.customization)
    def show_help_credits(self):
        """Show help overview"""
        HelpDialog(root,"Ballot Browser Credits",HelpMessages.credits)

    def show_help_license(self):
        """Show help overview"""
        HelpDialog(root,"Ballot Browser License",HelpMessages.license)

    def show_help_bugs(self):
        """Show help bugs"""
        HelpDialog(root,"Ballot Browser Bugs",HelpMessages.bugs)

    def show_help_signature(self):
        """Show help signature"""
        HelpDialog(root,"Ballot Browser Signature",HelpMessages.signature)

    def show_help_precinct(self):
        "Show help precinct"""
        HelpDialog(root,"Ballot Browser and Precincts",HelpMessages.precinct)

    def validate_image_file(self):
        """
        validate_image_file makes it easy (or easier) for a user
        to run gpg to test the provided vote image archive file
        against the signature file. It confirms the existence of gpg,
        tries to get our public key, and tries to validate the 
        image file archive named at App.archive_name.
        """
        # First, do we have gpg on our system?
        fullname = "gpg"
        if True: #os.name=='nt':
            HelpDialog(root,"GPG Help",HelpMessages.gpginfo)
        try:
            gpg = os.popen(
                "%s %s" % (fullname,
                           "--version"
                           )
                )
            outlines = "GPG results\non your system\n\n"
            if gpg is None:
                outlines += "No GPG"
            for l in gpg.readlines():
                outlines += l
            gpg.close()
            showinfo("GPG output from your system",outlines,App.root)
        except:
            tkMessageBox.showerror("GPG not found","Could not open gpg.")
            return
            
    def set_filename_extension(self, *args):
        App.filename_extension = askstring("Filename extension",
"""Enter the extension that ends
your image file names
(.jpg, .png, etc...)""","Enter extension:",App.root)
        if App.filename_extension.startswith("."):
            pass
        else:
            App.filename_extension = "."+App.filename_extension
        self.statusbar.push(self.contextid,"Filename extension set to: '%s'" % (App.filename_extension))
        
        if App.filename_extension.startswith("."):
            pass
        else:
            App.filename_extension = "."+App.filename_extension

    def set_delay_seconds(self, *args):
        self.delay_seconds = askinteger("Delay each ballot",
"""Enter the number of seconds
to leave each ballot on screen
before advancing to the next""","Enter delay:",self.delay_seconds)
        if self.delay_seconds == -1: self.delay_seconds = 1
        self.statusbar.push(self.contextid,"Delay set to: %s second(s)" % (self.delay_seconds))
        

    def every_twentieth(self, *args):
        """
        Toggle the Tkinter variable skip_count between 1 and 20
        """
        if App.skip_count==1:
            App.skip_count = 20
        else:
            App.skip_count = 1

    def listSelection(self,event):
        firstIndex = self.plist.curselection()[0]
        value = self.plist.get(firstIndex)
        print value
        # go through App.countedvotescsv or a derived file 
        # and locate all filenames that have this code
        try:
            code = value.split(",")[1]
        except:
            code = "000000000"
        votefile = open(App.countedvotescsv,"r")
        lasta = None
        App.all_images = []
        for l in votefile.xreadlines():
            a = l.split(",")[0]
            b = l.split(",")[1]
            if a != lasta and b[-8:] == code[-8:]:
                App.all_images.append(a)
            lasta = a
        App.on_deck_filename = App.all_images.pop()
        self.go_cb()


    def __init__(self,topwindow):
        """
        The GUI is assembled here.
        We provide the ability to specify a directory for files.
        For the case where files are in our standard format, we
        allow specification of starting and ending number for the count.
        After the initial run, if the user runs BuildVisualDict to give
        us precinct information, we can put up a listbox allowing 
        narrowing to a given precinct or set of precincts.
        """
	global s2
	global pixelwidth, pixelheight
        self.templates = {}

	self.number_dir = "." 
        self.show_vote_overlay = True
        self.show_contest_overlay = True
        self.show_choice_overlay = True
	self.count_all = False
        self.delay_seconds = 3
        self.contbutton = None
        self.spinbutton = None
        self.timeout = None

        self.leftmarkup = None
        self.rightmarkup = None
        self.leftimage = None
        self.rightimage = None
        self.leftfilename = None
        self.rightfilename = None
        self.leftnumber = None
        self.rightnumber = None
        self.leftbv = None
        self.rightbv = None
        self.nowentry = None


        App.root = topwindow
	#App.root.connect("delete_event", self.quitfromdelete, None)

        if const.use_db:
            try:
                App.dbc = db.PostgresDB(const.dbname, const.dbuser)
            except db.DatabaseError:
                util.fatal("Could not connect to database")


        self.rownum = 1
        self.canvas = None
        self.i = None

        vbox = gtk.VBox()
        App.root.add(vbox)
        App.root.connect("key_press_event", self.key_press_cb)
        self.statusbar = gtk.Statusbar()
        self.contextid = self.statusbar.get_context_id("main")
        vbox.pack_end(self.statusbar,False,True)
        self.statusbar.push(self.contextid,"Status: OK")
	self.base_dir_label = gtk.Label("Ballot root: .")
	self.base_dir_label.set_justify(gtk.JUSTIFY_LEFT)
	self.base_dir_label.set_alignment(0.,0.)
	vbox.pack_end(self.base_dir_label,False,False)
        ui = '''<ui>
    <menubar name="MenuBar">
      <menu action="File">
        <menuitem action="Quit"/>
      </menu>
      <menu action="Preferences">
        <menuitem action="Toggle contest overlay"/>
        <menuitem action="Toggle choice overlay"/>
      </menu>
    </menubar>
    </ui>'''
      
    #webbrowser.open("http://maps.google.com/maps?q=%f,+%f" % (42.995,-71.455))
    # Create a UIManager instance
        uimanager = gtk.UIManager()

    # Add the accelerator group to the toplevel window
        accelgroup = uimanager.get_accel_group()
        window.add_accel_group(accelgroup)

    # Create an ActionGroup
        actiongroup = gtk.ActionGroup('UIManagerExample')
        actiongroup = actiongroup

    # Create a ToggleAction, etc.
        actiongroup.add_toggle_actions(
            [
('Showx vote overlay', 
 None, 
 '_Showx vote overlay', 
 '<Control>s', 
'Showx vote overlay', 
self.show_vote_cb, 
True),
('Count all images', 
None, 
'Count _all images (careful!) inside folder...', 
 '<Control>a', 
'Select a folder and count all images, not just numbered files.', 
self.count_all_cb, 
False)])

    # Create actions
        actiongroup.add_actions(
[('Files from external list', gtk.STOCK_PASTE, 
  'Files from _external list', None,
  'External file list', self.files_from_external_file_list_cb),
 ('Files for precinct', None, 
  'Files for _precinct', None,
  'Files for precinct list', self.files_for_precinct_cb),
 ('Set ballot folder', gtk.STOCK_DIRECTORY, 
  'Set _ballot folder', None,
  'Set ballot folder', self.set_ballot_folder),
 ('Set filename extension', None, 
  'Set filename _extension', None,
  'Set filename extension', self.set_filename_extension),
 ('Delay each ballot', None, 
  '_Delay each ballot by...', None,
  'Set number of seconds to delay ballot', self.set_delay_seconds),
 ('Toggle contest overlay', None, 
  '_Toggle contest names...', None,
  'Toggle contest names', self.show_contest_cb),
 ('Toggle choice overlay', None, 
  '_Toggle candidate names...', None,
  'Toggle candidate names', self.show_choice_cb),
 ('Quit', gtk.STOCK_QUIT, 
  '_Quit', None,
  'Quit the Program', self.quitplease),
 ('Overview', gtk.STOCK_HELP, 
  '_Overview', None,
  'Overview', help_overview_cb),
 ('File', None, '_File'),
 ('Help', None, '_Help'),
 ('Lists', None, '_Lists'),
 ('Preferences', None, '_Preferences')])
        actiongroup.get_action('Quit').set_property('short-label', '_Quit')

    # Add the actiongroup to the uimanager
        uimanager.insert_action_group(actiongroup, 0)

    # Add a UI description
        uimanager.add_ui_from_string(ui)

    # Create a MenuBar
        menubar = uimanager.get_widget('/MenuBar')
        vbox.pack_start(menubar, False)

    # Create fields for start, end, current
        initial_zoom = 0.5
	hbox = gtk.HBox()
        buttonbox = gtk.HBox()
        boundsframe = gtk.Frame(label="Image Number")
        buttonframe = gtk.Frame(label="Single Step")
        autoframe = gtk.Frame(label="Auto Advance")
        zoomframe = gtk.Frame(label="Ballot Zoom")

        boundsbbox = gtk.HBox()
        #boundsbbox.pack_start(gtk.Label("Start"))
        #startentry = gtk.Entry()
        #startentry.set_max_length(7)
        #startentry.set_text("000001")
        #startentry.set_width_chars(7)
        #boundsbbox.pack_start(startentry)
        #boundsbbox.pack_start(gtk.Label("End"))
        #endentry = gtk.Entry()
        #endentry.set_max_length(7)
        #endentry.set_width_chars(7)
        #boundsbbox.pack_start(endentry)
        self.nowentry = gtk.Entry()
        #self.nowentry.set_editable(False)
        self.nowentry.set_text("000001")
        self.nowentry.set_max_length(7)
        self.nowentry.set_width_chars(7)
        self.nowentry.connect("activate",self.go_cb,None)
        boundsbbox.pack_start(self.nowentry)
        self.gobutton = gtk.Button("Go")
        self.gobutton.connect("clicked",self.go_cb,None)
        boundsbbox.pack_start(self.gobutton)
        prevbutton = create_arrow_button(gtk.ARROW_LEFT,gtk.SHADOW_IN)
        nextbutton = create_arrow_button(gtk.ARROW_RIGHT,gtk.SHADOW_IN)
        nextbutton.connect("clicked",self.next_cb,None)
        prevbutton.connect("clicked",self.prev_cb,None)

        buttonframebbox = gtk.HBox()
        buttonframebbox.pack_start(prevbutton,True)
        buttonframebbox.pack_start(nextbutton,True)

        autoframebbox = gtk.HBox()
        self.contbutton = gtk.CheckButton("every")
        self.contbutton.set_active(False)
        self.contbutton.connect("toggled",self.contbutton_cb, None)
        adj = gtk.Adjustment(1.0,1.0,60.0,1.0,5.0,0.0)
        self.spinbutton = gtk.SpinButton(adj)
        self.spinbutton.set_value(1)
        self.spinbutton.set_numeric(True)
        #self.timeout = gobject.timeout_add(1000,timeout_func,self,self.spinbutton)
        autoframebbox.pack_start(self.contbutton,False)
        autoframebbox.pack_start(self.spinbutton,False)
        autoframebbox.pack_start(gtk.Label("seconds"),False)

        zoomframebbox = gtk.HBox()
        adj = gtk.Adjustment(0.4,0.1,1.0,0.05,0.1,0.0)
        self.zoomslider = gtk.HScale(adjustment=adj)        
        self.zoomslider.set_digits(2)
        zoomframebbox.pack_start(self.zoomslider,True,True)
	self.zoomslider.connect("value-changed",self.zoom_update_cb,None)


        boundsframe.add(boundsbbox)
        buttonframe.add(buttonframebbox)
        autoframe.add(autoframebbox)
        zoomframe.add(zoomframebbox)
        buttonbox.pack_start(boundsframe,True)
        buttonbox.pack_start(buttonframe,True)
        buttonbox.pack_start(autoframe,True)
        buttonbox.pack_start(zoomframe,True)


        

        vbox.pack_start(buttonbox,False,False)
	vbox.pack_start(hbox, True,True)
        #controlbox = gtk.VBox()
	#controlbox.set_size_request(100,100)
        #hbox.pack_start(controlbox,False ,False)

	label_start = gtk.Label("Start:")
        self.entry_start = gtk.Entry()
	self.entry_start.set_max_length(8)
        self.entry_start.set_text("1")
	self.entry_start.set_size_request(50,25)

	label_end = gtk.Label("End:")
        self.entry_end = gtk.Entry()
	self.entry_end.set_max_length(8)
	self.entry_end.set_size_request(50,25)

	self.label_now1 = gtk.Label("Now:")
        self.label_now2 = gtk.Label("(none)")
	self.label_now2.set_size_request(150,25)
        go_button = gtk.Button("Go")
	go_button.connect("clicked",self.go_cb,None)
        done_button = gtk.Button("Done")
	done_button.connect("clicked",self.done_cb,None)
        pause_button = gtk.Button("Pause")
	pause_button.connect("clicked",self.pause_cb,None)
        flag_button = gtk.Button("Flag")
	flag_button.connect("clicked",self.flag_cb,None)
	# value, lower, upper, step_increment, page_increment, page_size
	# Note that the page_size value only makes a difference for
	# scrollbar widgets, and the highest value you'll get is actually
	# (upper - page_size).
	label_time = gtk.Label("Time to next")
	adj1 = gtk.Adjustment(.01, 0, 1.01, .01, .10, .10)
        self.pct_left_meter = gtk.HScale(adj1)
	self.pct_left_meter.set_draw_value(False)
        self.pct_left_meter.set_size_request(150,40)
	adj1.set_value(25)

	label_zoom = gtk.Label("Ballot size")

        #controlbox.pack_start(label_time,False,True)
        #controlbox.pack_start(self.pct_left_meter,False,True)
        #controlbox.pack_start(label_zoom,False,True)
        #controlbox.pack_start(self.zoomslider,False,True)
        #controlbox.pack_start(label_start,False,True)
        #controlbox.pack_start(self.entry_start,False,True)
        #controlbox.pack_start(label_end,False,True)
        #controlbox.pack_start(self.entry_end,False,True)
        #controlbox.pack_start(self.label_now1,False,True)
        #controlbox.pack_start(self.label_now2,False,True)
        #controlbox.pack_start(go_button,False,True)
        #controlbox.pack_start(done_button,False,True)
        #controlbox.pack_start(pause_button,False,True)
        #controlbox.pack_start(flag_button,False,True)

        App.current_folder = "."
        self.pw = gtk.HPaned()
        

        #self.leftimage = Image.open('unproc/000101.jpg')
        #self.rightimage = Image.open('unproc/000102.jpg')

        self.leftnumber = -1
        self.rightnumber = 0

        #self.leftfilename = 'proc/000101.jpg'
        #self.rightfilename = 'proc/000102.jpg'
        #self.leftdatafilename = 'results/000101.txt'
        #self.rightdatafilename = 'results/000101.txt' #sic
        #self.leftbv = BallotVotes(self.leftdatafilename,self.leftnumber)
        #self.rightbv = BallotVotes(self.rightdatafilename,self.rightnumber)
        #self.i1.set_from_file("unproc/000101.jpg")


	new_w = int(pixelwidth*initial_zoom)
	new_h = int(pixelheight*initial_zoom)

        # left scrolled window / drawing area
        self.sw1 = gtk.ScrolledWindow()
        self.i1window = None
        self.i1gc = None
        self.i1 = gtk.DrawingArea()
	self.i1.set_size_request(new_w,new_h)
        self.sw1.set_size_request(425,700)
	self.i1.width = new_w
	self.i1.height = new_h
        self.sw1.add_with_viewport(self.i1)

        # right scrolled window / drawing area
        self.sw2 = gtk.ScrolledWindow()
        self.i2window = None
        self.i2gc = None
        self.i2 = gtk.DrawingArea()
        self.i2.set_size_request(new_w,new_h)
	self.sw2.set_size_request(425,700)
	self.i2.width = new_w
	self.i2.height = new_h
	self.i2.width = new_w
	self.i2.height = new_h
        self.sw2.add_with_viewport(self.i2)

        self.i1.show()
        self.i2.show()
        self.i1.connect("expose_event",self.expose_cb,(1,self.leftimage))
        self.i1.connect("configure-event",self.configure_cb, (1,self.leftimage))
        self.i2.connect("expose_event",self.expose_cb,(2,self.rightimage))
        self.i2.connect("configure-event",self.configure_cb, (2,self.rightimage))
        #self.i1.connect("motion_notify_event", self.motion_notify_cb)
        self.i1.connect("button_press_event", self.button_press_cb1)
        self.i1.connect("key_press_event", self.key_press_cb)
        #self.i2.connect("motion_notify_event", self.motion_notify_cb)
        self.i2.connect("button_press_event", self.button_press_cb2)

        self.i1.add_events(gtk.gdk.EXPOSURE_MASK
                            | gtk.gdk.LEAVE_NOTIFY_MASK
                            | gtk.gdk.BUTTON_PRESS_MASK
                            | gtk.gdk.POINTER_MOTION_MASK
                            | gtk.gdk.POINTER_MOTION_HINT_MASK|gtk.gdk.KEY_PRESS_MASK)
        self.i2.add_events(gtk.gdk.EXPOSURE_MASK
                            | gtk.gdk.LEAVE_NOTIFY_MASK
                            | gtk.gdk.BUTTON_PRESS_MASK
                            | gtk.gdk.POINTER_MOTION_MASK
                            | gtk.gdk.POINTER_MOTION_HINT_MASK|gtk.gdk.KEY_PRESS_MASK)
        self.pw.add1(self.sw1)
        self.pw.add2(self.sw2)
        hbox.pack_start(self.pw,True,True)
        


def on_delete_event(widget, event):
    gtk.main_quit()
    sys.exit(0)


if __name__ == '__main__':
    # read configuration from tevs.cfg and set constants for this run
    cfg_file = get_args()

    # read configuration from tevs.cfg and set constants for this run
    config.get(cfg_file)
    logger = config.logger(const.logfilename)

    proc = util.root("proc")
    results = util.root("results")
    const.procformatstring = proc + "/%03d/%06d" + const.filename_extension
    const.unprocformatstring = const.incoming + "/%03d/%06d" + const.filename_extension
    const.resultsformatstring = results + "/%03d/%06d" + ".txt"
    window = gtk.Window(gtk.WINDOW_TOPLEVEL)
    window.connect("delete-event",on_delete_event)
    window.set_title("TEVS Ballot Browser, version %s" % (version,))
    app = App(window)
    window.show_all()
    gtk.main()

