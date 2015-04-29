#!/usr/bin/env python

# tevsgui_scan.py is normally called from the tevs GUI, via tevsgui_scan_svc.py
# It may be run standalone, taking command line arguments as follows:
# python tevsgui_scan.py duplex height_in_mm resolution endorser
# where duplex and endorser are True or False passed as strings
# and height_in_mm and resolution are integers passed as strings
# It prompts when ready for input with Scan--> and accepts:
# x -- meaning terminate
# Gnnn -- meaning set next scan to nnn and scan
# It prints out No paper found and sleeps 2 seconds if the scanner is empty.

import sane
import time
import pdb
import sys

class ScanningException(BaseException):
    def __init__(self, value):
        self.value = value
    def __str__(self):
            return repr(self.value)


class Scanner(object):
    def __init__(self, 
                 duplex, 
                 height_in_mm, 
                 resolution, 
                 image_loc_fmt_string,
                 endorser=False):
        self.duplex = duplex
        self.height_in_mm = int(height_in_mm)
        self.resolution = int(resolution)
        self.image_loc_fmt_string = image_loc_fmt_string
        if endorser.startswith("T"):
            self.endorser = True
        else:
            self.endorser = False

        sane.init()
        print "Init"
        sys.stdout.flush()
        devlist = sane.get_devices()
        if len(devlist)<1:
            print "No scanner found."
            sys.stdout.flush()
            sys.exit(0)
        self.s = sane.open(devlist[0][0])
        print "Devices"
        sys.stdout.flush()

        self.duplex = duplex
        if duplex.startswith("T"):
            self.s.source = 'ADF Duplex'
        else:
            self.s.source = 'ADF Front'
        self.s.endorser = self.endorser
        if self.s.endorser:
            self.s.endorser_string = '%08ud'
            try:
                self.s.endorser_bits = 24
            except Exception, e:
                print e
                sys.stdout.flush()
        self.s.page_height = height_in_mm
        self.s.br_y = height_in_mm
        self.s.mode = 'Color'
        self.s.resolution = resolution
        self.s.y_resolution = resolution
        self.s.swdeskew = 0 # software deskew might cause problems with our line recog
        # Gray at 140 took 3.1 sec
        # at 150 took 3.2 sec
        # at 200 took 4.0
        # at 220 took 5.1
        # at 240 took 3.2 sec
        # at 270 will not process properly
        # at 249 will not process properly

    def scan(self, counter):
        try:
            if not self.s.page_loaded:
                print "No paper loaded, sleeping 2 seconds."
                sys.stdout.flush()
                time.sleep(2)
                return None
        except AttributeError, e:
            pass
        try:
            if self.endorser:
                self.s.endorser_val = int(counter)
        except AttributeError, e:
            print e
            sys.stdout.flush()

        imgs = []
        try:
            self.s.start()
            imgs.append(self.s.snap(no_cancel=True))
        except sane.error, e:
            self.s.cancel() 
            raise ScanningException(e)
        if self.duplex:
            try:
                self.s.start()
                imgs.append(self.s.snap())
            except sane.error, e:
                self.s.cancel()
                raise ScanningException(e)
        self.s.cancel()
        return imgs

if __name__ == "__main__":
    if sys.argv<5:
        print "usage: python tevsgui_scan.py duplexTF heightmm resolution endorserTF image_loc_fmt_string"
    #print "tevsgui_scan.py starting"
    sys.stdout.flush()
    duplex = sys.argv[1]
    height_in_mm = int(sys.argv[2])
    resolution = int(sys.argv[3])
    endorser = sys.argv[4]
    #print "Dup",duplex,
    #print "Height",height_in_mm,
    #print "Resolution",resolution,
    #print "Endorser",endorser
    #print "Image loc fmt string",sys.argv[5]
    #print "NOTE: Fmt string must have one or two places for decimal arguments."
    if not sys.argv[5].find("%") >=0:
        sys.exit(0)
    scanner = Scanner(duplex, 
                      height_in_mm, 
                      resolution, 
                      image_loc_fmt_string=sys.argv[5],
                      endorser=endorser)
    #print "Scanner",scanner,"to",scanner.image_loc_fmt_string
    # receive commands from service, dispatch to scanner
    while True:
        print "Scan-->"
        sys.stdout.flush()
        x = sys.stdin.readline()
        #print x
        #sys.stdout.flush()
        # x to close
        if x.startswith("x"):
            break
        # Gnnn means scan with endorser starting at nnn
        elif x.startswith("G"):
            counter = int(x[1:])
            #print "GOT",counter
            #sys.stdout.flush()
            while True:
                try:
                    imgs = scanner.scan(counter)
                except ScanningException, e:
                    print e
                    sys.stdout.flush()
                    continue
                if imgs is None:
                    break
                for index,img in enumerate(imgs):
                    # save each image to appropriate filename
                    try:
                        img.save(scanner.image_loc_fmt_string % (index+counter,))
                    except TypeError:
                        img.save(scanner.image_loc_fmt_string % ((index+counter)/1000,index+counter,))
                print counter,"OK",
                counter += len(imgs)
                print counter
                sys.stdout.flush()
        elif x.startswith("?"):
            question_char = (x[1])
            if question_char == "D":
                print scanner.duplex
            elif question_char:
                pass
            sys.stdout.flush()
