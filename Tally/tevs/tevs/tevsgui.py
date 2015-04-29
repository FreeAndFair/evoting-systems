# NEXT: What's wrong with the transition from process_overvote to vote_count
#! /usr/bin/env python
# tevs gui

import sys
try:  
    import pygtk  
    pygtk.require("2.0")  
except:  
    pass  
try:  
    import gtk  
except:  
    print("GTK Not Available")
    sys.exit(1)
try:
    import vte
except:
    print("VTE Not Available")
    #sys.exit(2)

import time
import const
import config
import db
import db_overvotes
import db_merge_variants
import exceptions
import getopt
import gobject
import glib
import glob
import Image
import logging
import os
import pdb
import pickle
import util
import sane
import subprocess
# each "requestor" sets up and communicates with a subprocess 
# to handle tasks that would otherwise freeze the GUI
import tevsgui_db_query_requestor
import tevsgui_processing_requestor
import tevsgui_generic_requestor
import tevsgui_scan_requestor

import tevsgui_display_votes 
import tevsgui_status


# the requestors set up programs which store potentially lengthy 
# response data in python "pickle" files
# for reading by the main program
# when the main program is called back

global ambig_pickle_file
ambig_pickle_file = "/tmp/ambig.pickle"

global typecode_pickle_file
typecode_pickle_file = "/tmp/typecode.pickle"

global votecount_pickle_file
votecount_pickle_file = "/tmp/votecount.pickle"

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


# db setup for direct connections
def initialize_database():
    dbc = None
    try:
        dbc = db.PostgresDB(const.dbname, const.dbuser)
    except db.DatabaseError:
        util.fatal("Could not connect to database")
    return dbc

def on_delete_event(widget, event):
    return True

class tevsGui:

    # graphics setup
    gc = None
    cmap = None
    paginated_pages = 0
    lines_per_page = 15
    printfile = None
    printfilename = "/tmp/printfile.txt"
    green, red, blue, purple = None,None,None,None

    def initialize_gc(self,window):
        tevsGui.cmap = window.get_colormap()
        tevsGui.green = tevsGui.cmap.alloc_color("green")
        tevsGui.red = tevsGui.cmap.alloc_color("red")
        tevsGui.blue = tevsGui.cmap.alloc_color("blue")
        tevsGui.purple = tevsGui.cmap.alloc_color("purple")
        self.gc = window.new_gc(foreground=tevsGui.green)
            
        self.gc.set_line_attributes(2,
                                   gtk.gdk.LINE_SOLID,
                                   gtk.gdk.CAP_BUTT,
                                   gtk.gdk.JOIN_BEVEL)


    # GUI initial state
    # is configured from tevs.cfg height, width, and resolution info
    # set configuration to locked, set lock toggle on
    # start with pretty pix in left and right windows
    

    def expose_cb(self,drawarea,exposure,image_side):
        """draw image according to scale settings"""
        #print "Exposure, DrawingArea",drawarea
        #print "Image side",image_side

        w,h = drawarea.window.get_size()

        if self.gc is None:
            self.initialize_gc(drawarea.window)

        try:
            if image_side == 0:
                orig_width,orig_height = self.leftimage.size
                imagedpi = int(round(orig_width/const.ballot_width_inches))
                image = self.leftimage.resize(
                    (w,h)).convert("RGB")
                imagestr = image.tostring()
                bv = self.leftbv
            else:
                orig_width,orig_height = self.rightimage.size
                imagedpi = int(round(orig_width/const.ballot_width_inches))
                image = self.rightimage.resize(
                    (w,h)).convert("RGB")
                imagestr = image.tostring()
                bv = self.rightbv
            imagewidth, imageheight = image.size

            xscalefactor = float(w)/orig_width
            yscalefactor = float(h)/orig_height
            #print "W,H,IW,IH,XS,YS,DPI"
            #print w,h
            #print orig_width, orig_height
            #print xscalefactor,yscalefactor,imagedpi
            drawarea.window.draw_rgb_image(
                self.gc, 
                0, 0, 
                w, h, 
                gtk.gdk.RGB_DITHER_NONE, 
                imagestr, 
                w*3
                )

            if bv is not None:
                bv.paint(self,
                         drawarea,
                         xscalefactor,
                         yscalefactor,
                         imagedpi,
                         overlay_votes=self.overlay_votes.get_active(),
                         overlay_choices=self.overlay_choices.get_active() ,
                         overlay_contests = self.overlay_contests.get_active())
        except Exception, e:
            print e
        #drawarea.window.draw_line(self.gc, 0, 0, w, h);
        #drawarea.window.draw_line(self.gc, 0, 0, w, int(h*.9))
        #drawarea.window.draw_line(self.gc, w, 0, 0, h);
        #drawarea.window.draw_line(self.gc, w, 0, 0, int(h*.9))


    def configure_cb(self,drawarea,event,image_side):
        #print "Configure DrawingArea",drawarea
        #print "Event",event
        #print "Image side (client data)",image_side
        # from pygtk tutorial
        x,y,width,height = drawarea.get_allocation()
        #print x, y, width, height
        self.leftpixmap = gtk.gdk.Pixmap(drawarea.window,
                                         width,height)#drawarea.width,
                                         #drawarea.height) 
	# call expose callback to clean up
	self.expose_cb(drawarea,event,image_side)

    def button_press_cb1(self,button,data):
        self.button_press_cb(button,data)

    def button_press_cb2(self,button,data):
        self.button_press_cb(button,data)

    def button_press_cb(self,button,data):
        print "Button press."
        print button
        print data

    def key_press_cb(self,button,data):
        print "Key press."
        print button
        print data

    # adjustments
    def on_imprintOffsetAdjustment_changed(self,adj,data):
        self.builder.get_object("imprintOffsetScale").set_value(adj.get_value())
        self.status.update("Imprint offset now %d" % (int(adj.get_value())))

    def on_widthAdjustment_changed(self,adj,data):
        self.builder.get_object("widthScale").set_value(adj.get_value())
        self.status.update("Width now %d" % (int(adj.get_value())))

    def on_heightAdjustment_changed(self,adj,data):
        self.builder.get_object("heightScale").set_value(adj.get_value())
        self.status.update("Height now %d" % (int(adj.get_value())))

    def on_zoomAdjustment_changed(self,adj,data):
        self.builder.get_object("zoomScale").set_value(adj.get_value())
        #print data
        v = adj.get_value()
        v = float(v/10)
        self.status.update("Zoom now %d" % (int(adj.get_value())))
        self.zoom_value = v
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


    # toggles
    def on_autoAdvance_toggled(self, button, data):
        pass

    def on_doubleSided_toggled(self, button, data):
        pass

    def on_singleSided_toggled(self, button, data):
        pass

    def on_lowRes150_toggled(self, button, data):
        pass

    def on_hiRes300_toggled(self, button, data):
        pass

    def on_imprintOff_toggled(self, button, data):
        pass

    def on_imprintOn_toggled(self, button, data):
        pass

    def on_overlayVotes_toggled(self, button, data):
        self.expose_cb(self.i1,None,0)
        self.expose_cb(self.i2,None,1)

    def on_overlayContests_toggled(self, button, data):
        self.expose_cb(self.i1,None,0)
        self.expose_cb(self.i2,None,1)

    def on_overlayChoices_toggled(self, button, data):
        self.expose_cb(self.i1,None,0)
        self.expose_cb(self.i2,None,1)

    def on_configurationLock_toggled(self, button, data):
        sb = self.builder.get_object("statusbar1")
        sb.set_has_resize_grip(True)
        basic_cid = sb.get_context_id("Basic")
        sb.push(basic_cid,"Configuration lock toggled %s." % (
                str(button.get_active()),))
        print "Configuration lock toggled."
        print self
        print button, button.get_active()
        self.builder.get_object("configurationFrame").set_sensitive(
            button.get_active()
            )
        print data

    # clicked
    def on_symlinkDialog_okButton_clicked(self, button, data):
        print "Symlink dialog ok button clicked."
        print self
        #wildcard = self.builder.get_object("symlinkDialog_wildcardEntry").get_text()


# ***********************************************************************
# VOTE EXTRACTION
# ***********************************************************************

    def on_extractNow_clicked(self, button, data):
        print """We can do a call to find_intensity changes 
on the first image or image pair and show the resulting boxes, text,
and add in a report on the ballot type to use."""
        print "Extract now clicked."
        # start another Python running process_ballot_on_input.py,
        # sending it continual requests for more 
        # until it repeatedly runs out of available files
        pid = tevsgui_processing_requestor.set_up_extraction_process(
            self.status)
        self.status.update("Vote extraction started as process %d" % (pid,))


    def on_extractAsArrive_toggled(self, button, data):
        print "Extract as arrive toggled."
        print self
        self.extract_continually = button.get_active()
        if self.extract_continually:
            pid = tevsgui_processing_requestor.set_up_extraction_process(self.status,)
            self.status.update("Vote extraction started as process %d" % (pid,))
        else:
            tevsgui_processing_requestor.take_down_extraction_process()
            #self.status.update("Extraction ended.")



# ***********************************************************************
# SCANNING
# ***********************************************************************

    def on_searchForScanner_clicked(self, button, data):
        print "Search for scanner clicked."
        print self
        self.showScannerString()
        print button
        print data


    def scan_req_test_stdout_cb(self,line):
        """receive and display /tmp files """
        print "TEVSGUI TEST received: [",line,"]"
        oldnumber = 0
        newnumber = 0
        test_format_string = "/tmp/test%06d.jpg"
        if line.find(" OK ")>=0:
            # this means a ballot was scanned, update
            fields = line.split(" ")
            old_number = int(fields[0])
            new_number = int(fields[-1])
            # read in files from oldnumber to newnumber
            # as left and right images, force display
            for num in range(old_number,new_number):
                filename = test_format_string % (num,)
                if num==old_number: 
                    self.leftimage = Image.open(filename)
                    self.expose_cb(self.i1,None,0)
                else: 
                    self.rightimage = Image.open(filename)
                    self.expose_cb(self.i2,None,1)
            self.scanner.stop()
            self.scanner = None
        elif line.find("-->")>=0:
            # this is a prompt; respond by requesting more ballots
            print "(prompt)"
            try:
                counter = int(self.next_scan_number_entry.get_text())
                send_string = "G%d\n" % (counter,)
                self.scanner.send(send_string)
                print "Sent scanner",send_string
            except TypeError, e:
                print e
                print "Must enter only digits"
                counter = 1234

    def scan_req_stdout_cb(self,line,data):
        """handle dialog with scanner via ScanRequestor
        when we get a line with nnn OK mmm, the scanning
        program has written files nnn and needs no input to continue;
        when we get a line with -->, the scanning program is waiting
        for instruction: Gnnn to "Go" and start scanning again from nnn,
        or x to exit.
        """
        print "TEVSGUI received: [",line,"]"
        print "and registered data is",data
        #oldnumber = 0
        #newnumber = 0
        if line.find(" OK ")>0:
            # nnn OK nnn; a ballot was scanned, update
            fields = line.split(" ")
            old_number = int(fields[0])
            new_number = int(fields[-1])
            nextscanfile = "%s/nexttoscan.txt" % (util.root(),)
            os.unlink(nextscanfile)
            nsf = open(nextscanfile,"w")
            nsf.write("%d\n" % (new_number,))
            nsf.close()
            self.batch_count_number = new_number - self.batch_start_number
            self.status.update("Start of batch: %d Count in batch: %d" % (self.batch_start_number,self.batch_count_number))
            # read in files from oldnumber to newnumber
            # as left and right images, force display
            for num in range(old_number,new_number):
                filename = const.unprocformatstring % (
                    (num)/1000,(num))
                if num==old_number: 
                    self.leftimage = Image.open(filename)
                    self.expose_cb(self.i1,None,0)
                else: 
                    self.rightimage = Image.open(filename)
                    self.expose_cb(self.i2,None,1)
            self.last_scanned_number = old_number
            self.next_scan_number_entry.set_text("%s" % (new_number,))
        elif line.find("-->")>0:
            # this is a prompt; respond by requesting more ballots
            #print "Got prompt"
            
            try:
                counter = int(self.next_scan_number_entry.get_text())
                self.scanner.send("G%d\n" % (counter,))
            except TypeError, e:
                print e
                print "Must enter only digits"
                counter = 1234
                

    def scanner_setup(self,location_string,cb):
        (duplex,
         height_in_100th,width_in_100th,
         resolution,
         height_in_mm,width_in_mm,
         endorser) = self.get_scan_settings()

        if self.scanner is None:
            height_in_mm = 280
            self.scanner = tevsgui_scan_requestor.ScanRequestor(
                location_string,
                duplex = duplex,
                heightmm = height_in_mm,
                res = resolution,
                endorser = endorser,
                stdout_cb = cb)
        # handle reception of scans and request for more in cb

    def on_testScan_clicked(self, button, data):
        self.scanner_setup("/tmp/test%06d.jpg",
                           self.scan_req_test_stdout_cb)

    def on_scanStart_clicked(self, button, data):
        self.scanner_setup(const.unprocformatstring,
                           self.scan_req_stdout_cb)
        try:
            self.batch_start_number = int(self.builder.get_object("nextScanNumber").get_text())
            logger.info("Scanning from %d Note:%s\n" % (
                    self.batch_start_number,
                    self.builder.get_object("nextScanNoteEntry").get_text())
                        )
        except Exception, e:
            print e


    def on_scanRequestStop_clicked(self, button, data):
        print "Scan request stop clicked."
        self.scanner.stop()
        self.scanner = None

    def get_scan_settings(self):
        duplex = self.builder.get_object("doubleSided").get_active()

        height_in_100th = int(
            self.builder.get_object("heightScale").get_value())
        height_in_mm = int(.254 * height_in_100th)
        width_in_100th = int(
            self.builder.get_object("widthScale").get_value())
        width_in_mm = int(.254 * width_in_100th)

        r150 = self.builder.get_object("lowRes150").get_active()
        r300 = self.builder.get_object("hiRes300").get_active()
        if r150:
            resolution = 150
        elif r300:
            resolution = 300
        endorser = self.builder.get_object("imprintOn").get_active()
        return (duplex,
                height_in_100th,
                width_in_100th,
                resolution,
                height_in_mm,
                width_in_mm,
                endorser)
        
    def update_image_and_data(self,new_file,window_number=0):
        print "Display file changed to ",new_file,"in",window_number
        if window_number==0:
            imageobj = self.leftimage
            bvobj = self.leftbv
            self.image_number_entry.set_text(new_file[-10:-4]) 
            companion_filename_number = int(new_file[-10:-4])+1
            companion_filename = const.unprocformatstring % (
            companion_filename_number/1000,
            companion_filename_number)
        else:
            imageobj = self.rightimage
            bvobj = self.rightbv
        try:
            imageobj = Image.open(new_file)
        except Exception, e:
            try:
                imageobj = Image.open(new_file.replace("unproc","proc"))
            except Exception,e2:
                print e2
        image_number = int(new_file[-10:-4])
        bvobj = tevsgui_display_votes.BallotVotes(image_number,self.dbc)

        if window_number == 0:
            self.leftbv = bvobj
            self.leftimage = imageobj
            self.expose_cb(self.i1,None,0)
            try:
                self.rightimage = Image.open(companion_filename)
            except Exception, e:
                try:
                    self.rightimage = Image.open(companion_filename.replace("unproc","proc"))
                except Exception,e2:
                    print e2
            image_number = int(companion_filename[-10:-4])
            self.rightbv = tevsgui_display_votes.BallotVotes(image_number,self.dbc)
            self.expose_cb(self.i2,None,1)
        else:
            self.rightbv = bvobj
            self.rightimage = imageobj
            self.expose_cb(self.i2,None,1)
        
    def imageList_selection_changed(self,tvselection,data):
        tm,ti = tvselection.get_selected()
        selected_filename = tm.get_value(ti,0)
        self.update_image_and_data(selected_filename,0)
  
    def associate_selection_changed(self,tvselection,data):
        tm,ti = tvselection.get_selected()
        print "%s,%s,%s" % (tm.get_value(ti,0),tm.get_value(ti,1),tm.get_value(ti,2))

    def begin_print(self,printop,context,data):
        print "*****Begin Print*****"
        #print "Printop",printop
        #print "Context",context
        #print "Data",data
        print "*****Begin Print*****"
        self.printfile = open(self.printfilename,"w")
        self.status.update("Creating print file.")

    def end_print(self,printop,context,data):
        print "*****End Print*****"
        #print "Printop",printop
        #print "Context",context
        #print "Data",data
        self.printfile.write("\n.FINIS")
        self.printfile.close()
        self.printfile = None
        self.status.update("Generating PDF")
        p = subprocess.Popen("pdfroff -t -m om  --pdf-output=%s.pdf %s" % (self.printfilename,self.printfilename), shell=True)
        sts = os.waitpid(p.pid, 0)[1]
        self.status.update("Sending PDF to printer")
        p = subprocess.Popen("lpr " + self.printfilename, shell=True)
        sts = os.waitpid(p.pid, 0)[1]

    def request_page_setup(self,printop,context,page_number,setup,data):
        print "*****Request page setup",
        #print "Printop",printop
        #print "Context",context
        #print "Page",page_number
        #print "Setup",setup
        #print "Data",data


    def paginate(self,printop,context,data):
        print "*****Paginate",printop,context
        print "Data0 len",len(data[0]),"Data1 len",len(data[1])
        #print "Data0 first item",data[0][0],
        #print "Data1 first item",data[1][0]
        self.paginated_pages = len(data[0])/self.lines_per_page
        printop.set_n_pages(self.paginated_pages)
        print "set n pages to ",self.paginated_pages
        self.paginated_pages -= 1
        return (self.paginated_pages!=0)

    def draw_page(self,printop,context,page_number,data):
        print "****Draw Page",
        #print "Printop",printop
        #print "Context",context
        #print "Page number",page_number
        #print "Data for this page"
        if page_number == 0:
            self.printfile.write("""
.TITLE "Vote Count Summary "
.SUBTITLE "database %s"
.AUTHOR "TEVS"
.DOCTYPE DEFAULT
.PRINTSTYLE TYPESET
.PARA_SPACE
.INDENT_FIRST_PARAS
.PARA_INDENT 1m
.PAPER LETTER
.L_MARGIN .5i
.R_MARGIN .5i
.START
.NUMBER_HEADS
.NUMBER_SUBHEADS
.NUMBER_PARAHEADS
.HEADER_CENTER "%s"
.HEADER_RIGHT "Counts"
.HEAD "%s counts as of %s"
.TS
tab(:) box ;
nw(0.5i) nw(0.7i) lw(2.6i) lw(2.6i) .
""" % (const.dbname,time.asctime(),const.dbname,time.asctime()))
        else:
            self.printfile.write("""
.NEWPAGE
.TS
tab(:) box ;
nw(0.5i) nw(0.7i) lw(2.6i) lw(2.6i) .
""")

        for index in range(page_number * self.lines_per_page,
                           (page_number+1) * self.lines_per_page):

            count = data[0][index][0]
            jur = data[0][index][1]
            contest = data[0][index][2]
            choice = data[0][index][3]
            try:
                self.printfile.write("%d:%s:T{\n%s\nT}:T{\n%s\nT}\n" % (count,jur,contest[:20],choice[:20]))
            except:
                pass
        #try:
        #    outfile.write("%6d%20s%20s%20s\n" % data[1][page_number])
        #except:
        #    pass
        self.printfile.write("\n.TE\n")

    def do_print(self,button,data):
        # data is list_store
        print_op = gtk.PrintOperation()
        print_op.connect("begin_print",self.begin_print,data)
        print_op.connect("paginate",self.paginate,data)
        print_op.connect("request_page_setup",self.request_page_setup,data)
        print_op.connect("draw_page",self.draw_page,data)
        print_op.connect("end_print",self.end_print,data)
        res = print_op.run(gtk.PRINT_OPERATION_ACTION_PRINT_DIALOG, self.window)

        
    def do_hide(self,button,window):
        window.hide()
        
    def text_merge_done(self,button,data):
        "update voteops from merged text, then get vote counts"
        window, store = data
        window.hide()
        db_merge_variants.update_voteops_from_associations(self.dbc,store)
        self.get_vote_counts()

#*************************************************************************
# DATABASE FILTER QUERIES:
# Ambig only checkbox triggers database request, 
# updating table when request calls back.
#*************************************************************************

    def ambig_data_ready_cb(self,line,data):
        global ambig_pickle_file
        #print "Ambig data ready in /tmp/ambig.pickle"
        tv = self.builder.get_object("imageListTreeView")
        tm = self.builder.get_object("imageListTreeModel")
        tvsel = tv.get_selection()
        # initialize at first use
        if not self.imageListInitted:
            tvsel.connect("changed",self.imageList_selection_changed,0)

            cr0 = gtk.CellRendererText()
            tvc0 = gtk.TreeViewColumn("Matches")
            tv.append_column(tvc0)
            tvc0.pack_start(cr0,True)
            tvc0.set_attributes(cr0,text=0)
            self.imageListInitted = True # do not reinit
        tm.clear()
        picklefile = open(ambig_pickle_file,"rb")
        retval = pickle.load(picklefile)
        picklefile.close()
        os.unlink(ambig_pickle_file)
        for record in retval:
            tm.append(record)


    def multiple_data_ready_cb(self, line, data):
        queries = data[0]
        qindex = data[1]+1
        self.status.update("Overvote step %d of %d" % (qindex+1,len(queries)))
        if qindex < len(queries)-1:
            qr = tevsgui_db_query_requestor.QueryRequestor(
                stdout_cb =self.multiple_data_ready_cb,
                user = const.dbuser,
                database = const.dbname,
                query = queries[qindex],
                retfile = ambig_pickle_file,
                stdout_cb_data = (queries,qindex))
            
    def multiple_q(self,button,data):
        queries = [
"drop table if exists overvotes cascade;",
"drop table if exists overvote_ids cascade;",
"drop table if exists overvote_values cascade;",
"drop table if exists overvote_diffs cascade;",
"""select count(*) as votes, contest_text_standardized_id, filename 
    into overvotes 
    from voteops 
    where was_voted 
    group by contest_text_standardized_id, filename;
""",
"""
select v.voteop_id 
       into overvote_ids 
       from overvotes o 
       join voteops v 
       on o.contest_text_standardized_id = v.contest_text_standardized_id 
       join ocr_variants ocr on v.contest_text_standardized_id = ocr.id
       and o.filename = v.filename 
       where o.votes > ocr.max_votes_in_contest;
""",
"""
select v.voteop_id, 
       substring(v.filename,28,15) as filename ,
       substring(v.contest_text,1,30) as contest,
       substring(v.choice_text,1,30) as choice, 
       v.red_darkest_pixels as darkest, 
       v.red_mean_intensity as intensity 
       into overvote_values 
       from overvote_ids o join voteops v 
       on o.voteop_id = v.voteop_id where was_voted;
""",
"""
select a.*, b.voteop_id as b_voteop_id, 
       (a.intensity - b.intensity) as intensity_a_less_intensity_b 
       into overvote_diffs 
       from overvote_values a join overvote_values b 
       on a.contest = b.contest and a.filename=b.filename and a.choice != b.choice; 
""",
"""
update voteops 
       set was_voted = False, overvoted=False, suspicious=True 
       where voteop_id in 
       (select b_voteop_id 
       	       from overvote_diffs 
	       where intensity_a_less_intensity_b < -30);

""",
"""
update voteops 
       set was_voted = False, overvoted=False,
       suspicious = True
       where voteop_id in 
       (select voteop_id 
       	       from overvote_diffs 
	       where intensity_a_less_intensity_b > 30);

""",
"""
update voteops 
       set was_voted = True, 
       suspicious = True,
       overvoted = True,
       where voteop_id in 
       (select voteop_id 
       	       from overvote_diffs 
	       where (intensity_a_less_intensity_b <= 30) 
               and (intensity_a_less_intensity_b >= -30)
);

"""]
        qr = tevsgui_db_query_requestor.QueryRequestor(
            stdout_cb =self.multiple_data_ready_cb,
            user = const.dbuser,
            database = const.dbname,
            query = queries[0],
            retfile = ambig_pickle_file,
            stdout_cb_data = (queries,0))
        self.status.update("Overvote step %d of %d" % (1,len(queries)))

    def on_ambigOnly_toggled(self, button, data):
        global ambig_pickle_file
        #self.multiple_q(button,data)
        #return
        query_string = """
select distinct filename 
from voteops v join ballots b on v.ballot_id = b.ballot_id 
where was_voted and (suspicious or overvoted) order by filename
"""
        print "Ambig only toggled."
        toggled_on = button.get_active()
        if toggled_on :
            qr = tevsgui_db_query_requestor.QueryRequestor(
                stdout_cb = self.ambig_data_ready_cb,
                user = const.dbuser,
                database = const.dbname,
                query = query_string,
                retfile = ambig_pickle_file)
            self.status.update("Locating ambiguous ballots.")
        else:
            tm = self.builder.get_object("imageListTreeModel")
            print tm.clear()
            self.status.update("Ready.")


#*************************************************************************
# Typecode entry (enter key) triggers database request, 
# updating table when request calls back.
#*************************************************************************

    def typecode_data_ready_cb(self,line,data):
        global typecode_pickle_file

        tv = self.builder.get_object("imageListTreeView")
        tm = self.builder.get_object("imageListTreeModel")
        tvsel = tv.get_selection()
        # initialize at first use
        if not self.imageListInitted:
            tvsel.connect("changed",self.imageList_selection_changed,0)
            cr0 = gtk.CellRendererText()
            tvc0 = gtk.TreeViewColumn("Matches")
            tv.append_column(tvc0)
            tvc0.pack_start(cr0,True)
            tvc0.set_attributes(cr0,text=0)
            self.imageListInitted = True # do not reinit
        tm.clear()
        picklefile = open(typecode_pickle_file,"rb")
        retval = pickle.load(picklefile)
        picklefile.close()
        os.unlink(typecode_pickle_file)
        for record in retval:
            tm.append(record)
        self.status.update("Ready")

    def on_typeCodeEntry_activate(self, button, data):
        print "On type code entry activated"
        type_code = button.get_text()
        print button, "text is", type_code
        typecode_query = """
select distinct filename 
from voteops v join ballots b on v.ballot_id = b.ballot_id 
where precinct = '%s' or code_string='%s'
order by filename
""" %  (type_code,type_code)        
        tv = self.builder.get_object("imageListTreeView")
        tm = self.builder.get_object("imageListTreeModel")
                
        tm.clear()
        self.status.update("Locating ballots having type code %s" % (
                type_code,))
        qr = tevsgui_db_query_requestor.QueryRequestor(
            stdout_cb = self.typecode_data_ready_cb,
            user = const.dbuser,
            database = const.dbname,
            query = typecode_query,
            retfile = typecode_pickle_file)

    def on_sqlEntry_activate(self, button, data):
        print "On sql entry activated"
        sql_where_clause = button.get_text()
        print button, "text is", sql_where_clause
        sql_where_clause = sql_where_clause.replace(";","")
        sql_query = """
select distinct filename 
from voteops v join ballots b on v.ballot_id = b.ballot_id 
where 
%s
order by filename
""" %  (sql_where_clause,)        
        tm = self.builder.get_object("imageListTreeModel")
        tm.clear()
        self.status.update("Locating ballots where condition %s holds" % (
                sql_where_clause,))
        # Note uses same callback as typecode (as could ambig)
        qr = tevsgui_db_query_requestor.QueryRequestor(
            stdout_cb = self.typecode_data_ready_cb,
            user = const.dbuser,
            database = const.dbname,
            query = sql_query,
            retfile = typecode_pickle_file)

#*************************************************************************
# Votecount button triggers two database requests, 
# updating GUI table when request calls back.
#*************************************************************************

    def votecount_data2_ready_cb(self,line,data):
        """async queries complete, data available, display in table"""
        global votecount_pickle_file
        #print "Votecount2 cb"
        #print "Ambig data ready in /tmp/ambig.pickle"
        picklefile = open(votecount_pickle_file,"rb")
        retval = pickle.load(picklefile)
        picklefile.close()
        os.unlink(votecount_pickle_file)
        for record in retval:
            data.append(record)
        self.last_vote_counts.extend(retval)

        window = self.builder.get_object ("windowVoteCounts")
        window.connect("delete-event",on_delete_event)
        treeview = self.builder.get_object("voteCountsTreeView")
        treeview.set_model(data)

        printButton = self.builder.get_object("voteCountsPrint")
        # None,None had been retval1,retval2
        printButton.connect("clicked",self.do_print,(self.last_vote_counts,self.last_vote_counts))

        closeButton = self.builder.get_object("voteCountsClose")
        closeButton.connect("clicked",self.do_hide,window)

        if not self.votecountListInitted:
            cr0 = gtk.CellRendererText()
            tvc0 = gtk.TreeViewColumn("Votes")
            treeview.append_column(tvc0)
            tvc0.pack_start(cr0,True)
            tvc0.set_attributes(cr0,text=0)

            cr1 = gtk.CellRendererText()
            tvc1 = gtk.TreeViewColumn("Precinct")
            treeview.append_column(tvc1)
            tvc1.pack_start(cr1,True)
            tvc1.set_attributes(cr1,text=1)

            cr2 = gtk.CellRendererText()
            tvc2 = gtk.TreeViewColumn("Contest")
            treeview.append_column(tvc2)
            tvc2.pack_start(cr2,True)
            tvc2.set_attributes(cr2,text=2)

            cr3 = gtk.CellRendererText()
            tvc3 = gtk.TreeViewColumn("Choice")
            treeview.append_column(tvc3)
            tvc3.pack_start(cr3,True)
            tvc3.set_attributes(cr3,text=3)
            self.votecountListInitted = True

        window.show_all()
        self.status.update("Ready.")

        print "Last vote count consists of %d records." % (
            len(self.last_vote_counts),)


    def votecount_data1_ready_cb(self,line,data):
        global votecount_pickle_file
        #print "Votecount1 cb"
        self.status.update("Retrieving per-precinct data.")
        #print "Ambig data ready in /tmp/ambig.pickle"
        picklefile = open(votecount_pickle_file,"rb")
        retval = pickle.load(picklefile)
        picklefile.close()
        os.unlink(votecount_pickle_file)
        for record in retval:
            data.append(record)
        self.last_vote_counts = retval
        # make new async query to database, calling back when done
        qr = tevsgui_db_query_requestor.QueryRequestor(
            stdout_cb = self.votecount_data2_ready_cb,
            stdout_cb_data = data,
            user = const.dbuser,
            database = const.dbname,
            query = db_merge_variants.vote_count_query %("precinct","precinct,","precinct, " ),
            retfile = votecount_pickle_file)


    def process_overvotes(self,line,stage):
        stages = [
(db_merge_variants.update_id_contests_str,"Updating contest variants"),
(db_merge_variants.update_id_choices_str,"Updating choice variants"),
("drop table if exists overvotes cascade;","Dropping old tables"),
("drop table if exists overvote_ids cascade;","Dropping old tables"),
("drop table if exists overvote_values cascade;","Dropping old tables"),
("drop table if exists overvote_diffs cascade;","Dropping old tables"),
("""select count(*) as votes, contest_text_standardized_id, filename into overvotes from voteops where was_voted group by contest_text_standardized_id, filename;""","Determining votes per contest per ballot"),
("""select v.voteop_id into overvote_ids from overvotes o join voteops v on o.contest_text_standardized_id = v.contest_text_standardized_id join ocr_variants ocr on v.contest_text_standardized_id = ocr.id and o.filename = v.filename where o.votes > ocr.max_votes_in_contest;""","Getting ids of overvoted votes"),
("""select v.voteop_id, substring(v.filename,28,15) as filename , substring(v.contest_text,1,30) as contest, substring(v.choice_text,1,30) as choice,v.red_darkest_pixels as darkest, v.red_mean_intensity as intensity into overvote_values from overvote_ids o join voteops v on o.voteop_id = v.voteop_id where was_voted;
""","Getting intensity values of overvoted votes for comparison"),
("""select a.*, b.voteop_id as b_voteop_id,  (a.intensity - b.intensity) as intensity_a_less_intensity_b into overvote_diffs from overvote_values a join overvote_values b on a.contest = b.contest and a.filename=b.filename and a.choice != b.choice; ""","Determining darkness differences between overvoted votes"),
("""update voteops set was_voted = False, overvoted=False, suspicious=True where voteop_id in (select b_voteop_id from overvote_diffs where intensity_a_less_intensity_b < -30);
""","Selecting darker where there is major intensity difference"),
("""update voteops set was_voted = False, overvoted=False, suspicious = True where voteop_id in (select voteop_id from overvote_diffs where intensity_a_less_intensity_b > 30);
""","Selecting darker where there is major intensity difference"),
("""update voteops set was_voted = True, suspicious = True, overvoted = True, where voteop_id in (select voteop_id from overvote_diffs where (intensity_a_less_intensity_b <= 30) and (intensity_a_less_intensity_b >= -30)
);""","Setting overvoted for similarly darkened overvotes")
]
        
        print stage
        if stage == 0: 
            print "Stage 0"
        if stage < len(stages)-1:
            qr = tevsgui_db_query_requestor.QueryRequestor(
                stdout_cb = self.process_overvotes,
                stdout_cb_data = stage+1,
                user = const.dbuser,
                database = const.dbname,
                query = stages[stage+1][0],
                retfile = votecount_pickle_file)
            self.status.update("%s. %d tasks left." % (stages[stage+1][1],len(stages)-stage))
        else:
            #pdb.set_trace()
            self.status.update("Done processing overvotes")
            #db_merge_variants.update_voteops_from_associations(self.dbc,store)
            #pdb.set_trace()
            #self.status.update("Done merging variants")
            
            ls = gtk.ListStore(gobject.TYPE_LONG,
                               gobject.TYPE_STRING,
                               gobject.TYPE_STRING,
                               gobject.TYPE_STRING)
            try:
                self.last_vote_counts = []
            except Exception,e:
                print e
                pdb.set_trace()

            # make async query to database, calling back when done
            qr = tevsgui_db_query_requestor.QueryRequestor(
                stdout_cb = self.votecount_data1_ready_cb,
                stdout_cb_data = ls,
                user = const.dbuser,
                database = const.dbname,
                query = db_merge_variants.vote_count_query %("'ALL'","","" ),
                retfile = votecount_pickle_file)


    def get_vote_counts(self):
        " retrieve and display vote counts, and allow for printing"
        global votecount_pickle_file
        msg = self.builder.get_object("messagedialog_overvotes")
        msg.connect("delete-event",on_delete_event)
        response = msg.run()
        msg.hide()
        self.status.update("Retrieving full jurisdiction data.")
        if response == gtk.RESPONSE_YES:
            # either call here, or invoke program standalone via subprocess
            #db_overvotes.process_overvotes(self.dbc.conn)
            self.process_overvotes("",-1)

        else:

            ls = gtk.ListStore(gobject.TYPE_LONG,
                               gobject.TYPE_STRING,
                               gobject.TYPE_STRING,
                               gobject.TYPE_STRING)
            try:
                self.last_vote_counts = []
            except Exception,e:
                print e
                pdb.set_trace()


            # make async query to database, calling back when done
            qr = tevsgui_db_query_requestor.QueryRequestor(
                stdout_cb = self.votecount_data1_ready_cb,
                stdout_cb_data = ls,
                user = const.dbuser,
                database = const.dbname,
                query = db_merge_variants.vote_count_query %("'ALL'","","" ),
                retfile = votecount_pickle_file)


    def text_merge_associate(self,button,data):
        treeview = data[0]
        e1 = data[1]
        e2 = data[2]
        b2 = data[3]
        associations = data[4]
        # get the row to modify from e1
        try:
            e1_value = int(e1.get_text())
        except:
            print "Not an integer"
            return
        try:
            e2_value = int(e2.get_text())
        except:
            print "Not an integer"
            return
        tm = treeview.get_model()
        # set the value of the 1st field of row e1 (-1) to the value given in e2
        # assumes row numbering in database starts at 1
        tm[e1_value-1][1] = e2_value
        # send the update to the ocr_variants table in the db
        # associate first row mentioned standardized_id
        # with regular id of second row mentioned
        try:
            self.dbc.query_no_returned_values(
                """update ocr_variants 
set standardized_id = %d where id = %d""" % (e1_value,e2_value))
        except Exception,e:
            print e

    def is_variants_table_wanted(self):
        # if the ocr_variants table exists, you may not need to redo the merge
        retval = self.dbc.query("""select table_name 
from information_schema.tables 
where table_catalog = CURRENT_CATALOG 
and table_schema = CURRENT_SCHEMA 
and table_name = 'ocr_variants'""")
        if len(retval) == 0:
            return False

            # table exists, prompt to find out if user wants to re-create it
        msg = self.builder.get_object("messagedialog_ocr")
        msg.connect("delete-event",on_delete_event)
        response = msg.run()
        msg.hide()
        if response == gtk.RESPONSE_YES:
            # rebuild table
            return True
        return False
        

    def on_buildVariantsTable_clicked(self, button, data):
        window = self.builder.get_object ("windowTextMerge")
        window.connect("delete-event",on_delete_event)
        treeview = self.builder.get_object("textMergeTreeView")


        associations = db_merge_variants.create_ocr_variants_list(self.dbc)
        ls_contests = gtk.ListStore(
            gobject.TYPE_LONG,
            gobject.TYPE_LONG,
            gobject.TYPE_STRING,
            gobject.TYPE_STRING)
        treeview.set_model(ls_contests)
        tvselection = treeview.get_selection()
        tvselection.connect("changed",self.associate_selection_changed,0)

        for record in associations:
            ls_contests.append(record)
        e1=self.builder.get_object("textMergeEntry1")
        e2=self.builder.get_object("textMergeEntry2")
        b1 = self.builder.get_object("textMergeApply")
        b2 = self.builder.get_object("textMergeClose")
        b1.connect("clicked",self.text_merge_associate,(treeview,e1,e2,b2,associations))
        b2.connect("clicked",self.text_merge_done,(window,ls_contests))

        if not self.variantsListInitted:
            cr0 = gtk.CellRendererText()
            tvc0 = gtk.TreeViewColumn("Row #")
            treeview.append_column(tvc0)
            tvc0.pack_start(cr0,True)
            tvc0.set_attributes(cr0,text=0)

            cr1 = gtk.CellRendererText()
            tvc1 = gtk.TreeViewColumn("Standard ID")
            treeview.append_column(tvc1)
            tvc1.pack_start(cr1,True)
            tvc1.set_attributes(cr1,text=1)

            cr2 = gtk.CellRendererText()
            tvc2 = gtk.TreeViewColumn("Contest Text")
            treeview.append_column(tvc2)
            tvc2.pack_start(cr2,True)
            tvc2.set_attributes(cr2,text=3)
            self.variantsListInitted = True
        window.show_all()

    def on_showVoteCounts_clicked(self, button, data):
        print "Show vote counts clicked."

        print self
        print button
        print data

        # to generate useful vote counts, we have to have the ability
        # to merge variants of contest text that occur on different 
        # templates.  We need user involvement, but can do much prior
        # to displaying to user.
        
        vtw = self.is_variants_table_wanted()

        if vtw:
            self.on_buildVariantsTable_clicked(None,None)
            # when close button is pressed, 
            # we proceed to the callback at "text_merge_done"
            # which calls get vote counts for us

        else:
            self.get_vote_counts()



    def on_printVoteCounts_clicked(self, button, data):
        print "Print vote counts clicked."
        print "Same SQL as for showVotes, feed csv into table, probably in Reportlab"
        print self
        print button
        print data
        retval1 = [
("a","b","c"),
("1","2","3"),
("4","5","6")
]
        retval2 = [
("2a","2b","2c"),
("21","22","23"),
("24","25","26")
]

        self.do_print(button,(retval1,retval2))

    def on_writingToDVD_clicked(self, button, data):
        print "Writing to DVD clicked."
        print "Send the growisofs command to the vte terminal"
        self.vte.feed_child("growisofs -dry-run -Z /dev/dvdrw1 /tmp/fordvd*\n")

    def on_generateSigningKey_clicked(self, button, data):
        print "Generate signing key clicked"
        print "Send gpg --gen-key to the vte terminal"
        self.vte.feed_child("gpg --gen-key\n")

    def on_createDatabaseDump_clicked(self, button, data):
        print "Create database backup clicked"
        self.vte.feed_child("pg_dump --create -- file %s.sql %s\n" % ((os.path.join(const.root, const.database), const.dbname)))

    def on_buildArchive_clicked(self, button, data):
        print "Create archive clicked"
        self.vte.feed_child("tar cvzf %s /tmp/fordvd.tgz\n" % (const.root,))

    def on_signingFiles_clicked(self, button, data):
        print "Signing files clicked"
        print "Send gpg --sign to the vte terminal"
        self.vte.feed_child("gpg --detach-sign /tmp/fordvd.tgz\n")

    def on_cewCloseButton_clicked(self,button,data):
        self.window1.hide()
        self.dialogCEW.hide()

    def on_saveToDVD_clicked(self, button, data):
        #if self.window1 is None:
        if True:
            self.window1 = gtk.Window()
            self.window1.connect("delete-event",on_delete_event)
            self.window1.set_title("TEVS Linux Command Window")
            self.vte = vte.Terminal()
            self.window1.add(self.vte)
            self.vte.fork_command()
            self.dialogCEW = self.builder.get_object("dialogCommandEntryWindow")
            self.dialogCEW.set_title("TEVS Linux Command Assistant")
            self.add_vte_here = self.builder.get_object("add_vte_here")
            
        self.window1.show_all()
        self.dialogCEW.show_all()
        self.window1.present()
        self.dialogCEW.present()
        #self.vte.feed_child("man growisofs\n")

#*************************************************************************
# IMAGE NAVIGATION
#*************************************************************************

    def on_gotoImage_clicked(self, button, data):
        print "Go to image clicked."
        print "If restrictions on images exist (check onlyAmbig, typeCodeEntry, sqlEntry, etc...)"
        print "get next item from local store returned by current query"
        print "otherwise, get next number"
        print "Retrieve image(s) into leftimage and rightimage,"
        print "Lookup vote information for new images."
        print self
        print button
        print data
        self.on_imageNumberEntry_activate(self.image_number_entry,data)


    def on_nextImage_clicked(self, button, data):
        print "Next image clicked."
        num_text=self.image_number_entry.get_text()
        num = int(num_text)+2
        self.image_number_entry.set_text("%d" % (num,))
        self.on_imageNumberEntry_activate(self.image_number_entry,data)

    def on_prevImage_clicked(self, button, data):
        print "Prev image clicked."
        print self
        print button
        print data
        num_text=self.image_number_entry.get_text()
        num = int(num_text)-2
        self.image_number_entry.set_text("%d" % (num,))
        self.on_imageNumberEntry_activate(self.image_number_entry,data)

    def on_imageNumberEntry_activate(self, button, data):
        print "On image number entry activated"
        print button, "text is", button.get_text()
        print data
        num_text = button.get_text()
        try:
            num = int(num_text)
            filename = const.unprocformatstring % (num/1000,num)
            self.update_image_and_data(filename,0)
        except Exception, e:
            print e

    def on_nextScanNumber_activate(self, button, data):
        print "On next scan number activated"
        print button, "text is", button.get_text()
        print data
        
    def on_nextScanNoteEntry_activate(self, button, data):
        print "On next scan number activated"
        print button, "text is", button.get_text()
        print data
        
    def on_rootFolder_current_folder_changed(self, button, data):
        print "On root folder current folder changed."
        print button
        print "Current folder",button.get_current_folder()
        print "Need to write change to config file and restart TEVS."
        print data

    def on_symlinkFromDirectoryChooser_current_folder_changed(self, button, data):

        print "On symlinkFromDirectory current folder changed."
        print "Returning, because of wierdness"
        return

        print button
        chosen_folder = button.get_current_folder()
        print "Current folder",chosen_folder
        dialog = self.builder.get_object("symlinkFromDialog")
        root_folder = self.builder.get_object("rootFolder").get_current_folder()
        response_id = dialog.run()
            
        if response_id == 1:
            try:
                wildcard = self.builder.get_object(
                    "symlinkDialog_wildcardEntry").get_text()
                print "Create symlinks to %s/%s files in %s/unproc tree." % (
                    chosen_folder,wildcard,root_folder)
                pdb.set_trace()
                pathlist = glob.glob("%s/%s" % (chosen_folder,wildcard))
                index = 0
                for p in pathlist:
                    try:
                        if not os.path.exists(
                            "%s/unproc/%03d" % (
                                root_folder,index/1000)
                            ):
                            os.makedirs("%s/unproc/%03d" % (
                                    root_folder,
                                    index/1000)
                                        )
                        if not os.path.exists(
                            "%s/unproc/%03d/%06d%s" % (
                                root_folder,
                                index/1000,
                                index,
                                p[p.rindex("."):]
                                )):
                            os.symlink(
                                p,
                                "%s/unproc/%03d/%06d%s" % (root_folder,
                                                           index/1000,
                                                           index,
                                                           p[p.rindex("."):])
                                )
                        index += 1
                    except ValueError, e:
                        print e
            except Exception, e:
                print e
            # create symlinks"
            dialog.hide()

    def on_autoAdvanceSeconds_value_changed(self,button,data):
        print "On auto advance seconds value changed."
        print "Value now %d" %(button.get_value_as_int(),)
        print data

    def showScannerString( self ):
        process_output = subprocess.Popen(["/usr/bin/scanimage",
                                           "--list-devices"],
                                          stdout=subprocess.PIPE).communicate()[0]
        process_output = process_output.replace("is a","\nis a")
        if process_output.find("No scanner")>-1:
            process_output = "NO SCANNER FOUND.\nCheck cabling and power\nif you'd like to scan."
        self.builder.get_object("scannerIDLabel").set_text(process_output)


    def __init__( self, dbc, logger ):
        # data base connection is handed in on creation
        self.dbc = dbc
        self.logger = logger
        self.scanner = None
        self.batch_start_number = 0
        self.batch_count_number = 0
        # user interface is in external file tevsgui.glade
        self.builder = gtk.Builder()
        self.builder.add_from_file("tevsgui.glade")
        self.window = self.builder.get_object ("windowMain")
        self.window.set_title("TEVS (GUI version) 20111004")
        
        # placeholders for uncreated windows
        self.dialogCEW = None
        self.window1 = None
        self.vte = None

        # set imageList initted True when you first create an image list
        # in response to user request for sublist of images
        self.imageListInitted = False

        # set votecountList initted True when you first create a vote count
        # in response to user request for sublist of images
        self.votecountListInitted = False

        # set variantsList initted True when you first create a set of OCR
        # variants in response to user request for merge or vote count
        self.variantsListInitted = False

        self.zoom_value = 0.1

        
        if self.window:
            self.window.connect("destroy", gtk.main_quit)

        self.overlay_votes = self.builder.get_object("overlayVotes")
        self.overlay_choices = self.builder.get_object("overlayChoices")
        self.overlay_contests = self.builder.get_object("overlayContests")



        # the root folder widget has as its current_folder value
        # the root folder from the tevs.cfg configuration file,
        # which points to the top of the tree containing unprocessed
        # and processed ballots and results.
        self.root_folder = self.builder.get_object("rootFolder")
        self.root_folder.set_current_folder(util.root())

        # last_scanned_number is set to the FIRST (sic) image 
        # of the LAST scanned sheet, as is last_processed_number
        self.last_scanned_number = None
        self.last_processed_number = None

        # the image_number_entry object shows 
        # the number of the image to DISPLAY on exposure or activity
        self.image_number_entry = self.builder.get_object("imageNumberEntry")

        # the next_scan_number_entry object shows
        # the number that will be used for the next image SCANNED
        self.next_scan_number_entry = self.builder.get_object("nextScanNumber")
        # retrieve its initial value from the file nexttoscan.txt in root
        nextscanfile = "%s/nexttoscan.txt" % (util.root(),)
        try:
            nsf = open(nextscanfile,"r")
            nsf_text = nsf.readline().strip()
            nsf.close()
            self.next_scan_number_entry.set_text(nsf_text)
        except:
            print "No next scan number file at",nextscanfile
            pass

        # If the symlink source folder is changed from the root folder,
        # we create, in the root folder unproc tree, one numbered link 
        # for every image file in the alternate symlink source folder.
        # This allows for easy import of externally built files
        # if they are named sequentially.
        self.symlink_source_folder = self.builder.get_object(
            "symlinkFromDirectoryChooser")
        self.symlink_source_folder.set_current_folder(util.root())

        # when toggled on, we have a separate subprocess running
        # which extracts votes from scans
        self.extract_continually = False

        # status is presented to the user via self.status.update("News")
        sb = self.builder.get_object("statusbar1")
        self.status = tevsgui_status.Status(sb)

        # try connecting to a scanner with scanimage;
        # show what scanimage returns 
        try:
            self.showScannerString()
        except Exception as e:
            print e

        # building vote counts is expensive, so keep them around once built
        self.last_vote_counts = []
            
        # configuration area should always start insensitive
        self.builder.get_object("configurationFrame").set_sensitive(False)


        # sw1, sw2 are the two scrolled windows containing drawing areas
        self.sw1 = self.builder.get_object("scrolledwindow1")
        self.sw2 = self.builder.get_object("scrolledwindow2")
        # i1, i2 are the drawing areas
        self.i1,self.i2 = None,None
        # i1window, i2window are the low level drawables in the drawing areas
        self.i1window, self.i2window = None,None
        # leftimage and rightimage are PIL images 
        # containing the files currently requested for display
        self.leftimage, self.rightimage = None, None
        # leftbv and rightbv are the BallotVotes lists 
        # associated with the files currently requested for display
        self.leftbv = None
        self.rightbv = None


        # left drawing area created within scrolledwindow1
        self.i1gc = None
        self.i1 = gtk.DrawingArea()
        self.sw1.set_size_request(425,700)
        self.sw1.add_with_viewport(self.i1)
        self.i1window = self.i1.window

        # right scrolled drawing area created within scrolledwindow2
        self.i2gc = None
        self.i2 = gtk.DrawingArea()
	self.sw2.set_size_request(425,700)
        self.sw2.add_with_viewport(self.i2)
        self.i2window = self.i2.window

        # have the drawing areas request as many pixels 
        # as there are in their images, but we don't have images yet
        self.i1.set_size_request(1000,1500)
        self.i2.set_size_request(1000,1500)
        self.i1.show()
        self.i2.show()

        try:
            self.leftimage = Image.open("/tmp/left.jpg")
            self.rightimage = Image.open("/tmp/right.jpg")
        except:
            self.leftimage = Image.new("RGB",(1000,1500),(255,0,0))
            self.rightimage = Image.new("RGB",(1001,1500),(0,0,255))
        self.i1.connect("expose_event",self.expose_cb,0)
        self.i1.connect("configure-event",self.configure_cb, 0)
        self.i2.connect("expose_event",self.expose_cb,1)
        self.i2.connect("configure-event",self.configure_cb, 1)
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

        # set toggles to initial values spec'd in config file:
        self.builder.get_object("doubleSided").set_active(const.num_pages==2)
        self.builder.get_object("singleSided").set_active(const.num_pages==1)
        self.builder.get_object("lowRes150").set_active(const.dpi==150.)
        self.builder.get_object("hiRes300").set_active(const.dpi==300.)

        # set sliders to initial values spec'd in config file
        for text,val in (("widthAdjustment",const.ballot_width_inches*100),
                     ("heightAdjustment",const.ballot_height_inches*100),
                     ("imprintOffsetAdjustment",const.imprint_offset_inches*100.),
                     ("zoomAdjustment",5.)
                         ):

            scale = self.builder.get_object(text.replace("Adjustment","Scale"))
            adj = self.builder.get_object(text)
            adj.set_value(val)
            scale.set_value(val)



        # MAY NEED A WAY TO MAKE SURE 
        # EVERYTHING ABOVE HAS COMPLETED
        # PRIOR TO REGISTERING CALLBACKS
        # We keep landing, bizarrely, in on_symlinkFromDirectoryChooser_set_file
        # Standard way of setting up callbacks, didn't work for us
        #dic = {
        #    "on_buttonQuit_clicked" : self.quit,
        #    "on_buttonAdd_clicked" : self.add,
        #    "on_buttonAdd_activate" : self.add,
        #    "on_windowMain_destroy" : self.quit,
        #    }
        #self.builder.connect_signals( dic )

        connex = ( 
            ("widthAdjustment",            #object name to GtkBuilder XML
             "on_widthAdjustment_changed", #signal in builder, not used
             "value-changed",              # signal
             self.on_widthAdjustment_changed), #callback in program
            ("heightAdjustment",
             "on_heightAdjustment_changed", 
             "value-changed", 
             self.on_heightAdjustment_changed),
            ("zoomAdjustment",
             "on_zoomAdjustment_changed", 
             "value-changed", 
             self.on_zoomAdjustment_changed),
            ("imprintOffsetAdjustment",
             "on_imprintOffsetAdjustment_changed", 
             "value-changed", 
             self.on_imprintOffsetAdjustment_changed),
            ("autoAdvance",
             "NI",
             "toggled",
             self.on_autoAdvance_toggled),
            ("overlayVotes",
             "NI",
             "toggled",
             self.on_overlayVotes_toggled),
            ("overlayContests",
             "NI",
             "toggled",
             self.on_overlayContests_toggled),
            ("overlayChoices",
             "NI",
             "toggled",
             self.on_overlayChoices_toggled),
            ("ambigOnly",
             "NI",
             "toggled",
             self.on_ambigOnly_toggled),
            ("extractAsArrive",
             "NI",
             "toggled",
             self.on_extractAsArrive_toggled),
            ("configurationLock",
             "NI",
             "toggled",
             self.on_configurationLock_toggled),
            ("doubleSided",
             "NI",
             "toggled",
             self.on_doubleSided_toggled),
            ("singleSided",
             "NI",
             "toggled",
             self.on_singleSided_toggled),
            ("lowRes150",
             "NI",
             "toggled",
             self.on_lowRes150_toggled),
            ("hiRes300",
             "NI",
             "toggled",
             self.on_hiRes300_toggled),
            ("imprintOn",
             "NI",
             "toggled",
             self.on_imprintOn_toggled),
            ("imprintOff",
             "NI",
             "toggled",
             self.on_imprintOff_toggled),
            ("searchForScanner",
             "NI",
             "clicked",
             self.on_searchForScanner_clicked),
            ("symlinkDialog_okButton",
             "NI",
             "clicked",
             self.on_symlinkDialog_okButton_clicked),
            ("scanStart",
             "NI",
             "clicked",
             self.on_scanStart_clicked),
            ("scanRequestStop",
             "NI",
             "clicked",
             self.on_scanRequestStop_clicked),
            ("testScan",
             "NI",
             "clicked",
             self.on_testScan_clicked),
            ("extractNow",
             "NI",
             "clicked",
             self.on_extractNow_clicked),
            ("buildVariantsTable",
             "NI",
             "clicked",
             self.on_buildVariantsTable_clicked),
            ("showVoteCounts",
             "NI",
             "clicked",
             self.on_showVoteCounts_clicked),
            ("cewSaveToDVD",
             "NI",
             "clicked",
             self.on_saveToDVD_clicked),
            ("cewCloseButton",
             "NI",
             "clicked",
             self.on_cewCloseButton_clicked),
            ("cewGenerateSigningKey",
             "NI",
             "clicked",
             self.on_generateSigningKey_clicked),
            ("cewCreateDatabaseDump",
             "NI",
             "clicked",
             self.on_createDatabaseDump_clicked),
            ("cewBuildArchive",
             "NI",
             "clicked",
             self.on_buildArchive_clicked),
            ("cewSigningFiles",
             "NI",
             "clicked",
             self.on_signingFiles_clicked),
            ("cewWritingToDVD",
             "NI",
             "clicked",
             self.on_writingToDVD_clicked),
            ("gotoImage",
             "NI",
             "clicked",
             self.on_gotoImage_clicked),
            ("prevImage",
             "NI",
             "clicked",
             self.on_prevImage_clicked),
            ("nextImage",
             "NI",
             "clicked",
             self.on_nextImage_clicked),
            ("imageNumberEntry",
             "NI",
             "activate",
             self.on_imageNumberEntry_activate),
            ("typeCodeEntry",
             "NI",
             "activate",
             self.on_typeCodeEntry_activate),
            ("sqlEntry",
             "NI",
             "activate",
             self.on_sqlEntry_activate),
            ("nextScanNumber",
             "NI",
             "activate",
             self.on_nextScanNumber_activate),
            ("nextScanNoteEntry",
             "NI",
             "activate",
             self.on_nextScanNoteEntry_activate),
            ("symlinkFromDirectoryChooser",
             "NI",
             "current-folder-changed",
             self.on_symlinkFromDirectoryChooser_current_folder_changed),
            ("rootFolder",
             "NI",
             "current-folder-changed",
             self.on_rootFolder_current_folder_changed)
        )
        for x in connex:
            try:
                self.builder.get_object(x[0]).connect(x[2],x[3],None)
            except Exception, e:
                print x
                print e
                pdb.set_trace()
        self.status.update("Ready")
  
    def quit(self, widget):
        sys.exit(0)
        

if __name__ == "__main__":
    # read configuration from tevs.cfg and set constants for this run
    cfg_file = get_args()
    config.get(cfg_file)
    logger = config.logger(const.logfilename)

    proc = util.root("proc")
    results = util.root("results")
    const.procformatstring = proc + "/%03d/%06d" + const.filename_extension
    const.unprocformatstring = const.incoming + "/%03d/%06d" + const.filename_extension
    const.resultsformatstring = results + "/%03d/%06d" + ".txt"
    # set up db connection and pass to gui
    dbc = None
    if const.use_db:
        dbc = initialize_database()
    tevsGui = tevsGui(dbc,logger)
    tevsGui.window.show()
    gtk.main()
