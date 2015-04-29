# HartBallot.py implements the interface defined (well, suggested)
# in Ballot.py, in a Hart-specific way.
# The Trachtenberg Election Verification System (TEVS)
# is copyright 2009,2010 by Mitch Trachtenberg 
# and is licensed under the GNU General Public License version 2.
# (see LICENSE file for details.)

import os
import pdb
import sys
import subprocess
import time
import math

import site; site.addsitedir(os.path.expanduser("~/tevs")) #XXX
import Image, ImageStat
from find_line import find_line
from line_util import *
from hart_util import *
from hart_build_contests import *
from hart_barcode import *
import Ballot
import const

from cropstats import cropstats

def adj(a):
    return int(round(float(const.dpi) * a))
    

class HartBallot(Ballot.Ballot):
    """Class representing ballots from Hart Intersystems.

    Each Hart ballot has dark rectangles around voting areas,
    and voting areas are grouped in boxed contests.
    """

    brand = "Hart"

    def __init__(self, images, extensions):
        #convert all our constants to locally correct values
        self.min_contest_height = adj(const.minimum_contest_height_inches)
        self.vote_target_horiz_offset = adj(const.vote_target_horiz_offset_inches)
        self.writein_xoff = adj(2.5) #XXX
        self.writein_yoff = adj(.6)
        self.allowed_corner_black = adj(const.allowed_corner_black_inches)
        super(HartBallot, self).__init__(images, extensions)

    def flip(self, im):
        # crop the upper bar code possibilities,
        # UL and UR run from y = .8" to beyond 1.5"
        # (try relying on only first two)
        # U/LL from 1/3" to 2/3", U/LR 1/3" to 2/3" inch in from right
        # note humboldt 2011 8.5 x 11 barcode channels less than 2/3"
        # ballot is rightside up if the missing bar code
        # is the upper right, upside down if the missing
        # barcode is lower left.

        # if we get even a third of a bar code, 
        # it should darken crop by more than 1/8

        # Not added: ambiguous results could be tested with OCR

        mean = lambda i: ImageStat.Stat(i).mean[0]
        box = lambda a, b, c, d: \
            mean(im.crop((adj(a), adj(b), adj(c), adj(d))))

        uls = box(.4, .8, .5, 1.5)
        ul2s = box(.3, .8, .5, 1.5)        
        urs = mean(im.crop((
            im.size[0] - adj(0.45), adj(0.8),
            im.size[0] - adj(0.4), adj(1.5)
        )))
        bar_cutoff = 224 #XXX should be in config
        if uls < bar_cutoff or ul2s < bar_cutoff:
            if urs < bar_cutoff:
                try:
                    print "FLIPPED IMAGE"
                    self.log.info("FLIPPED IMAGE")
                except Exception:
                    pass
                im = im.rotate(180)
        return im

    def find_landmarks(self, page):
        """ retrieve landmarks for Hart images, set tang, xref, yref

        Landmarks for the Hart Ballot will be the ulc, urc, lrc, llc 
        (x,y) pairs marking the four corners of the main surrounding box."""
        TOP=True
        BOT=False
        LEFT=True
        RIGHT=False
        #tiltinfo, from upperleft clockwise:
        #[(x,y),(x,y),(x,y),(x,y)] or None
        tiltinfo = []
        left_starting_x_offset = 2 * const.dpi
        right_starting_x_offset = page.image.size[0] - int(2.5 * const.dpi)
        if right_starting_x_offset <= int(const.dpi * .34):
            raise Ballot.BallotException(
                "Image width of %d pixels at %d dpi unexpectedly narrow." % (
                    page.image.size[0],
                    const.dpi)
                )

        hline = scan_strips_for_horiz_line_y(page.image, 
                                             const.dpi, 
                                             left_starting_x_offset, 
                                             const.dpi/2, const.dpi/2,
                                             TOP)
        tiltinfo.append(follow_hline_to_corner(page.image, 
                                               const.dpi, 
                                               left_starting_x_offset, 
                                               hline, LEFT))
        hline = scan_strips_for_horiz_line_y(page.image, 
                                             const.dpi, 
                                             right_starting_x_offset, 
                                             const.dpi/2, const.dpi/2, 
                                             TOP)
        tiltinfo.append(follow_hline_to_corner(page.image, 
                                               const.dpi, 
                                               right_starting_x_offset,
                                               hline, RIGHT))
        hline=scan_strips_for_horiz_line_y(page.image, 
                                           const.dpi, 
                                           right_starting_x_offset, 
                                           const.dpi/2, const.dpi/2, 
                                           BOT)
        tiltinfo.append(follow_hline_to_corner(page.image, 
                                               const.dpi, 
                                               right_starting_x_offset,
                                               hline, RIGHT))
        hline=scan_strips_for_horiz_line_y(page.image, 
                                           const.dpi, 
                                           left_starting_x_offset, 
                                           const.dpi/2, const.dpi/2, 
                                           BOT)
        tiltinfo.append(follow_hline_to_corner(page.image, 
                                               const.dpi, 
                                               left_starting_x_offset,
                                               hline, LEFT))
        # removing PILB call
        #tiltinfo = page.image.gethartlandmarks(const.dpi, 0)
        if tiltinfo is None or tiltinfo[0][0] == 0 or tiltinfo[1][0] == 0:
            page.blank = True #needs to ensure it is a page somehow
            self.log.info("Nonballot page at %s " % (page,))
            return 0.0, 0, 0, 0

        # flunk ballots with more than 
        # allowed_corner_black_inches of black in corner
        # to avoid dealing with severely skewed ballots

        errmsg = "Dark %s corner on %s"
        testlen = self.allowed_corner_black
        xs, ys = page.image.size

        #boxes to test
        ul = (0,             0,           
              testlen,       testlen)
 
        ur = (xs - testlen,  0,           
              xs - 1,        testlen)

        lr = (xs - testlen,  ys - testlen,
              xs - 1,        ys - 1)
 
        ll = (0,             ys - testlen,
              testlen,       ys - 1)

        for area, corner in ((ul, "upper left"),
                             (ur, "upper right"),
                             (lr, "lower right"),
                             (ll, "lower left")):
            if ImageStat.Stat(page.image.crop(area)).mean[0] < 16:
                raise Ballot.BallotException(errmsg % (corner, page.filename))

        xoff = tiltinfo[0][0]
        yoff = tiltinfo[0][1]

        shortdiff = tiltinfo[3][0] - tiltinfo[0][0]
        longdiff  = tiltinfo[3][1] - tiltinfo[0][1]
        hypot = math.sqrt(shortdiff*shortdiff + longdiff*longdiff)
        if longdiff != 0:
            rot = shortdiff/float(longdiff)
        else:
            rot = 0
        if abs(rot) > const.allowed_tangent:
            raise Ballot.BallotException(
                "Tilt %f of %s exceeds %f" % (rot, page.filename, const.allowed_tangent)
            )
        self.log.debug("tiltinfo/landmarks: %s" % (tiltinfo,))
        page.tiltinfo = tiltinfo
        return rot, xoff, yoff, hypot

    def get_layout_code(self, page):
        """ Determine the layout code(s) from the ulc barcode(s) """
        # barcode zones to search are from 1/3" to 1/6" to left of ulc
        # and from 1/8" above ulc down to 2 5/8" below ulc.

        third_inch, sixth_inch, eighth_inch = adj(.3333), adj(.1667), adj(.125)
        half_inch = adj(.5)
        # don't pass negative x,y into getbarcode
        if page.xoff < third_inch:
            raise Ballot.BallotException("bad xref")
        if page.yoff < eighth_inch:
            raise Ballot.BallotException("bad yref")
        # pass image, x,y,w,h
        try:
            barcode = hart_barcode(
                page.image,
                page.xoff - third_inch,
                page.yoff - eighth_inch,
                sixth_inch,
                eighth_inch + int(round((15.*const.dpi)/6.)) # bar code 2 1/3"
                )
        except BarcodeException as e:
            self.log.info("%s %s" % (page.filename,e))
            barcode = "NOGOOD"
        if not good_barcode(barcode):
            # try getting bar code from ocr of region beneath
            self.log.debug("Barcode no good, trying to get barcode via OCR")
            zone = page.image.crop((
                    page.xoff - third_inch - adj(.05),
                    page.yoff + adj(2.5),
                    page.xoff - adj(.04),
                    page.yoff + adj(4.5)
                    ))
            zone = zone.rotate(-90) #make it left to right
            barcode = self.extensions.ocr_engine(zone)

            #remove OCR errors specific to text guranteed numeric
            for bad, good in (("\n", ""),  (" ", ""),  ("O", "0"), ("o", "0"),
                              ("l",  "1"), ("I", "1"), ("B", "8"), ("Z", "2"),
                              ("]",  "1"), ("[", "1"), (".", ""),  (",", "")):
                barcode = barcode.replace(bad, good)

            if not good_barcode(barcode):
                raise Ballot.BallotException("bad bar code")

        return barcode

    def build_layout(self, page):
        """ get layout and ocr information """
        image = page.image
        dpi = const.dpi
        first_line = page.tiltinfo[0][0]
        last_line =  page.tiltinfo[1][0]
        width = last_line - first_line
        first_third = first_line + width/3
        second_third = first_line + (2*width)/3
        print "Warning: assuming three columns"
        print first_line,first_third,second_third,last_line
        rot90 = image.rotate(-90.)
        rot90.save("/tmp/rot90.jpg")
        pot_line = [0,0,0,0]
        search_start_y = dpi/3
        vlines = []
        while pot_line is not None:
            try:
                pot_line = find_line(rot90,
                                     rot90.size[0]/2,
                                     search_start_y,
                                     search_npixels = (rot90.size[1]/2),
                                     threshold=64, 
                                     black_sufficient=True)
                if pot_line is not None:
                    search_start_y = pot_line[1]+(const.dpi/16)
                print pot_line
                vlines.append((pot_line[1]+pot_line[3])/2)
            except Exception, e:
                print e
                pdb.set_trace()
        #vlines = [first_line,first_third,second_third,last_line]
        #column_width = width/3
        column_width = vlines[2] - vlines[1]
        vthop = int(round(const.vote_target_horiz_offset_inches * const.dpi))
        contests = []
        for vline in vlines[:-1]:
            croplist = (vline,0,vline+column_width,image.size[1])
            crop = image.crop(croplist)
            pot_hlines = find_all_horiz_lines(crop,dpi)
            # normally, pull the .07 from config.vote_box_horiz_offset_inches
            vboxes = gethartvoteboxes(image,vline+vthop,dpi/2,dpi)
            column_contests = hart_build_contests(page.image,
                                                  pot_hlines,
                                                  vboxes,
                                                  vline,
                                                  column_width,
                                                  dpi,
                                                  extensions = self.extensions)
            contests.extend(column_contests)
        for contest in contests:
            self.log.debug("%d,%d, %s" % (contest.x,contest.y,contest.description))
            #print contest.x, contest.y, contest.description
            for choice in contest.choices:
                self.log.debug(" %d,%d, %s" % (choice.x,choice.y,choice.description))
                #print " ", choice.x, choice.y, choice.description


        return contests


    def xvendor_level_adjustment(self,page,image,x,y,w,h):
        """Return precise x,y of ulc of target given crop containing target"""
        contig_pixels_required = 2
        # target left wall will occupy leftmost 1/10"
        # find start of black range 
        # continuing downwards for 1/2 target height
        # and rightwards for 1/2 target width
        crop = image.crop((x,y,x+w,y+h))
        # start halfway down the crop, move right until dark for wall width
        # test at three vertical offsets to reduce likelihood of being tricked
        test_y1 = crop.size[1]/2
        test_y2 = (crop.size[1]/2) - (const.dpi/50)
        test_y3 = (crop.size[1]/2) + (const.dpi/50)
        contig = 0
        valid_x = -1
        let = const.line_exit_threshold
        for test_x in range(0,crop.size[0]/2):
            if (
                (crop.getpixel((test_x,test_y1))[0] < let)
                and (crop.getpixel((test_x,test_y2))[0] < let)
                and (crop.getpixel((test_x,test_y3))[0] < let)):
                contig += 1
            if contig >= contig_pixels_required:
                valid_x = test_x - (contig - 1)
                break
        if valid_x < 0:
            #problem
            pass
        # now move up in wall until end, and if needed down until end
        contig = 0
        valid_top_y = -1
        for test_y in range(crop.size[1]/2,0,-1):
            ok = False
            if crop.getpixel((valid_x+1,test_y))[0] >= const.line_exit_threshold:
                contig += 1
            if contig > contig_pixels_required:
                test_top_y = test_y + contig
                # confirm dark for at least 1/4 crop width pixels
                # found believable ulc x,y
                ok = True
                for test_x in range(valid_x+1,valid_x + (crop.size[0]/4)):
                    # add 1 pix to get back into black, one for slip
                    try:
                        red = crop.getpixel((test_x,test_top_y+2))[0]
                    except IndexError as e:
                        self.log.debug("VLA FAILED, returning passed values.")
                        self.log.debug(
                            "Xrange %d to %d, test %d, %d, cropsize %d,%d" % (
                                valid_x+1,
                                valid_x + (crop.size[0]/2),
                                test_x,
                                test_top_y+2,
                                crop.size))
                        return x,y
                    if red > const.line_exit_threshold:
                        ok = False
                        break
                if ok: 
                    valid_top_y = test_top_y+1
                    break
        if valid_top_y < 0:
            #problem
            valid_top_y = 0
        else:
            return x+valid_x, y+valid_top_y
        # top of target might be outside crop, check for bottom
        contig = 0
        valid_bottom_y = crop.size[1]-1
        for test_y in range(crop.size[1]/2,crop.size[1],1):
            if crop.getpixel((valid_x+1,test_y))[0] >= const.line_exit_threshold:
                contig += 1
            if contig > contig_pixels_required:
                valid_bottom_y = test_y - contig
                break
        return x + valid_x, y + valid_bottom_y - (const.target_height_inches * const.dpi) 

            
def good_barcode(code_string):
    """check code for obvious flaws"""
    if code_string is None:
        return False
    if len(code_string) != 14:
        return False
    elif not (code_string.startswith("100") 
              or code_string.startswith("200")):
        # disqualify if not a sheet 1 or a sheet 2
        return False
    elif code_string[7] != "0":
        return False

    # ninth digit is side count, must be four or below
    # and everything should be decimal digits as well
    try:
        csi = int(code_string[8])
        _ = int(code_string[8:])
    except ValueError:
        return False
    return csi <= 4

