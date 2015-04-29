#!/usr/bin/env python

import sane
import time
import sys
import getopt
import os
from string import atoi
from datetime import datetime

import const
import config
import util
import next

# scanloop.py: scan files into the unproc directory tree
# the -s argument gives the starting number 
# to assign to scans and the -e argument gives the number which,
# once assigned, should terminate scanning
# If no start number is specified, or the start is 0,
# the program pulls the next number from nexttoscan.txt in the current
# directory.

# Note that when extraction.py processes files in the unproc directory tree
# it moves each processed file to the proc directory tree.

# Note that when scanning in duplex, you have to start, snap(no cancel), 
# then start, snap to get the second side

class ScanningException(Exception):
    pass

class Scanner(object):
    def __init__(self, duplex, height_in_mm, resolution):
        sane.init()
        errstring = ""
        s = sane.open(sane.get_devices()[0][0])
        if duplex:
            s.source = 'ADF Duplex'
        else:
            s.source = 'ADF Front'
        s.endorser = True
        s.endorser_string = '%08ud'
        s.page_height = height_in_mm
        s.br_y = height_in_mm
        s.mode = 'Color'
        s.resolution = resolution
        s.y_resolution = resolution
        # be ready to remove this if it does not properly set reported dpi
        s.swdeskew = 0 # software deskew might cause problems with our line recog
        # Gray at 140 took 3.1 sec
        # at 150 took 3.2 sec
        # at 200 took 4.0
        # at 220 took 5.1
        # at 240 took 3.2 sec
        # at 270 will not process properly
        # at 249 will not process properly
        self.s = s
        self.duplex = duplex

    def _scan(self, i):
        if i > 10:
            raise ScanningException(self.errstring)
        try:
            self.s.start()
        except sane.error:
            self.errstring = sane.error
            self.s.cancel()
            #print "Will wait two seconds"
            time.sleep(2)
            self._scan(i+1)

    def scan(self, counter):
        try:
            self.s.endorser_val = counter
            self._scan(1)
            imgs = []
            if self.duplex:
                imgs.append(self.s.snap(no_cancel=True))
                self._scan(1)
            imgs.append(self.s.snap())
            return imgs
        except ScanningException,e:
            print e
            raise

def args():
    counter = 0
    duplex = False
    comment = ""
    inches = 11
    resolution = 300
    try:
        opts, args = getopt.getopt(
            sys.argv[1:], 
            "s:e:d:l:r:c:",
            ["start=",
             "end=",
             "duplex=",
             "length=",
             "resolution=",
             "comment="
            ]
        )
    except getopt.GetoptError:
        sys.stderr.write(
            "Usage: scanloop [-s #] [-e #] [-d True|False] [-l <length in inches>] [-r <dpi>][-c <comment>]\n"
        )
        sys.exit(2)
    for opt, arg in opts:
        if opt in ("-s","--start"):
            counter = int(arg)
        if opt in ("-d","--duplex"):
            duplex = arg.find("True") > -1
        if opt in ("-c","--comment"):
            comment = arg
        if opt in ("-l","--length"):
            inches = int(arg)
        if opt in ("-r","--resolution"):
            resolution = int(arg)
    return counter, duplex, comment, inches, resolution

def main(counter, duplex, comment, inches, resolution):
    # read configuration from tevs.cfg and set constants for this run
    const.debug = False #XXX
    config.get("tevs.cfg")
    util.mkdirp(const.root)
    log = config.logger(util.root("scan.log"))

    inches_to_mm = 25.4
    inc = 1
    if duplex:
        inc = 2
    num = next.IncrementingFile(util.root("nexttoscan.txt"), inc)
    try:
        scanner = Scanner(
            duplex,
            int(inches * inches_to_mm),
            resolution
        )

        while True:
            counter = num.value()
            print "Scanning",counter
            stamp = datetime.now().isoformat()
            for i, img in enumerate(scanner.scan(counter)):
                #get path
                n = counter + i
                p = "%03d" % (n/1000,)
                f = "%06d" % n
                dir = util.root(const.incoming, p)
                util.mkdirp(dir)
                filename = os.path.join(dir, f + ".jpg")
                img.save(filename)
                print "Saved",filename
                log.info("Saved %s at %s\n%s", filename, stamp, comment)
            num.increment_and_save()
    except ScanningException:
        print "Empty feeder?"
        log.info("Scan aborted due to empty feeder for 20 seconds.")
        sys.exit(2)
    except KeyboardInterrupt:
        log.info("Scan aborted by user")
        sys.exit(1)

if __name__ == "__main__":
    main(*args())

