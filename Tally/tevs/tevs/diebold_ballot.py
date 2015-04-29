# diebold_ballot.py implements the DuplexBallot interface 
# in Ballot.py for ballots following the style used in 
# Diebold/Premier. 
# The Trachtenberg Election Verification System (TEVS)
# is copyright 2009, 2010 by Mitch Trachtenberg 
# and is licensed under the GNU General Public License version 2.
# (see LICENSE file for details.)
"""
"""


import Ballot
import const
from adjust import rotator
from cropstats import cropstats
import Image, ImageStat
import pdb
import sys
from demo_utils import *
from line_util import *
from diebold_util import *

def adj(a):
    return int(round(float(const.dpi) * a))

def elim_halftone(x):
    if x>64:
        retval = 255
    else:
        retval = 0
    return retval


class DieboldBallot(Ballot.DuplexBallot):
    """Class representing Diebold duplex and single-sided ballots.

    The file name diebold_ballot.py and the class name DieboldBallot
    correspond to the brand entry in tevs.cfg (diebold.cfg), 
    the configuration file.
    """

    def __init__(self, images, extensions):
        #convert all our constants to locally correct values
        # many of these conversions will go to Ballot.py,
        # extenders will need to handle any new const values here, however
        # this is the size of the printed vote target's bounding box
        # add these margins to the vote target's bounding box 
        # when cropping and analyzing for votes
        self.min_contest_height = adj(const.minimum_contest_height_inches)
        self.vote_target_horiz_offset = adj(const.vote_target_horiz_offset_inches)
        self.writein_xoff = 0 #XXX
        self.writein_yoff = adj(-.1)
        self.allowed_corner_black = adj(const.allowed_corner_black_inches)
        self.back_upper_right_plus_x = 0
        self.back_upper_right_plus_y = 0
        self.left_landmarks = []
        self.right_landmarks = []
        super(DieboldBallot, self).__init__(images, extensions)

    def vendor_level_adjustment(self, page, image, x, y, w, h):
        """Given prelim xy offsets of target w margins, fine adjust target."""

        # check strip at center to look for either filled or empty oval;
        # recenter vertically
        darkened = 245
        crop = page.image.crop((x,y,w,h))
        stripe = crop.crop(
            ((crop.size[0]/2),
             0,
             (crop.size[0]/2)+1,
             crop.size[1]-1)
            )
        before_oval = 0
        after_oval = 0
        oval = 0
        stripedata = list(stripe.getdata())
        for num,p in enumerate(stripedata):
            if p[0] > darkened:
                before_oval += 1
            else:
                try:
                    test_offset = before_oval+printed_oval_height
                    if ((stripedata[test_offset-2][0] < darkened) or 
                        (stripedata[test_offset-1][0] < darkened) or 
                        (stripedata[test_offset][0] < darkened) or
                        (stripedata[test_offset+1][0] < darkened) or
                        (stripedata[test_offset+2][0] < darkened)):
                        oval_start = num
                        oval_end = num + printed_oval_height
                        after_oval = (
                            stripe.size[1] 
                            - (oval_start+printed_oval_height))
                        break
                except IndexError:
                    break
        #print cropy,before_oval,oval,after_oval
        afterlessbefore = int(round((after_oval - before_oval)/2))
        if abs(afterlessbefore)>2:
            cropy -= afterlessbefore
            #print "Adjusted",cropy
            crop = page.image.crop((
                cropx - page.margin_width,
                cropy - page.margin_height,
                min(cropx + page.margin_width + page.target_width,
                    page.image.size[0]-1),
                min(cropy + page.margin_height + page.target_height,
                    page.image.size[1]-1)
                ))
        self.log.debug("Result after final adj: (%d,%d)" % (cropx,cropy))
        return cropx, cropy


    # Extenders do not need to supply even a stub flip
    # because flip in Ballot.py will print a stub message in the absence
    # of a subclass implementation
    #def flip(self, im):
    #    # not implemented for Demo
    #    print "Flip not implemented for Demo."
    #    return im

    def find_landmarks(self, page):
        """just dup find_front_landmarks"""
        return self.find_front_landmarks(page)

    def find_back_landmarks(self, page):
        """just dup find_front_landmarks"""
        try:
            retval = self.find_front_landmarks(page)
        except Ballot.BallotException as e:
            page.blank = True
            retval = [0,0,0]
        return retval

    def find_front_landmarks(self, page):
        """Diebold ballots have dashes across the top and down the sides.

        The dashes occupy the leftmost .2" of a .25" zone and 
        and the uppermost .05" of a .25" zone.

        The uppermost dashes begin approximately 0.5" from the top,
        and the top edge of the lowermost dashes 
        is approximately 0.5" from the bottom. 

        The lowermost edge dashes are level with a series of dashes
        along the bottom which represent the layout code.

        A thinline appears approximately 0.15" below the top of the
        uppermost dashes; this is the upper line of boxes surrounding
        the main material.  Unfortunately, the boxes may not form a
        single rectangle.

        There is text underneath the center part of the bottom dashes.

        The side dashes extend very nearly to the edges of the image;
        the better landmarks are their inboard edges, as opposed to 
        their outboard edges.

        Vote ovals are approximately 0.1" tall by 0.2" wide and are
        centered vertically on the centerlines of side dashes.

        Vote ovals may be printed in a color other than black.
        Marin: vote ovals are printed in red

        Column widths are not uniform: Marin 3 column may be 2.75", 2.75", 2.5"

        Allow for 1/4" vertical slippage by scanning for top and bottom dashes
        from 1/4" to 3/4" from the top and bottom.  Treat the top of the 
        first identified dash line as the upper y landmarks.

        Allow for 1/4" horizontal slippage by locating the last x at which
        a reliable .05" dark .2" white pattern appears for one inch beneath 
        the identified top dash row and treating that as the ulc landmark x;
        do the same scanning from the outside edge in to identify the urc 
        landmark y.

        Store the upper left x,y coordinates of EACH timing mark dash
        to allow greater accuracy in locating the vote ops.

        """
        iround = lambda a: int(round(float(a)))
        dash_height = adj(0.05)
        dash_width = adj(0.20)
        dash_stride = adj(0.25)
        # search just under 1/2" - 1/20" from edge
        search_offset_from_edge = adj(0.43)
        # for testing, 
        # treat page argument as image if it has no image attribute
        try:
            im = page.image
        except:
            im = page
        # generate ulc, urc, lrc, llc coordinate pairs
        landmarks = []
        # find upper left line; scan down
        top_left_y = scan_strip_for_dash_y(im,
                                           const.dpi,
                                           const.dpi/2, #starting_x 
                                           const.dpi/4, #starting_y
                                           const.dpi/2, #height_to_scan
                                           top=True)
        # anticipate lower line will be at im.size[1] - const.dpi
        bot_left_y = scan_strip_for_dash_y(im,
                                           const.dpi,
                                           0, # can't count on inboard dashes
                                           const.dpi/4, #y from bottom
                                           const.dpi/2, #height_to_scan
                                           top=False)
        bot_left_y -= dash_height
        # anticipate lower line will be at im.size[1] - const.dpi/2, 
        # or that the two will be separated by the im.size[1] - const.dpi
        expected_y = top_left_y + im.size[1] - const.dpi
        if abs(expected_y - bot_left_y) > (const.dpi/10):
            print "Expected y", expected_y, "but bottom y", bot_left_y
            pdb.set_trace()

        # find upper left line; scan down
        top_right_y = scan_strip_for_dash_y(im,
                                                   const.dpi,
                                                   im.size[0] - const.dpi/2, #starting_x 
                                                   const.dpi/4, #starting_y
                                                   const.dpi/2, #height_to_scan
                                                   top=True)
        # anticipate lower line will be at im.size[1] - const.dpi
        bot_right_y = scan_strip_for_dash_y(im,
                                                   const.dpi,
                                                   im.size[0] - const.dpi/4 - 1, #starting_x 
                                                  const.dpi/4, #y from bot
                                                  const.dpi/2, #height_to_scan
                                                  top=False)
        bot_right_y -= dash_height
        # anticipate lower line will be at im.size[1] - const.dpi
        expected_y = top_right_y + im.size[1] - const.dpi
        if abs(expected_y - bot_right_y) > (const.dpi/10):
            print "Expected y", expected_y, "but bottom y", bot_right_y
            pdb.set_trace()

        # starting at top_left_y and top_right_y, 
        # locate landmark x's by scanning for vertical dash pattern
        top_left_x = find_top_landmark_dash(
            page, 
            search_offset_from_edge,
            top_left_y + (dash_height/2),
            const.dpi)
        top_right_x = find_top_landmark_dash(
            page,
            page.image.size[0] - search_offset_from_edge,
            top_right_y + (dash_height/2),
            const.dpi)

        bot_left_x = find_bottom_landmark_dash(page,
                                               0,
                                               bot_left_y + (dash_height/2),
                                               const.dpi)
        bot_right_x = find_bottom_landmark_dash(page,
                                               page.image.size[0]-1,
                                               bot_right_y + (dash_height/2),
                                               const.dpi)
        # landmarks list 
        # built from inboard upper coordinates 
        # of the four dashes at ends of dash sequences,
        # counterclockwise from upper left corner
        landmarks = [(top_left_x,top_left_y),
                     (top_right_x,top_right_y),
                     (bot_right_x,bot_right_y),
                     (bot_left_x, bot_left_y)
                     ]
        # we don't store here
        #self.landmarks = landmarks
        longdiff = landmarks[3][1] - landmarks[0][1]
        shortdiff = landmarks[3][0] - landmarks[0][0]
        r = float(shortdiff)/float(longdiff)
        # we depend on back landmarks being processed after front
        self.back_upper_right_plus_x = landmarks[1][0]
        self.back_upper_right_plus_y = landmarks[1][1]
        self.log.debug("landmarks %s,rot %f,(%d,%d), longdiff %d" % (landmarks,r,top_left_x,top_left_y,longdiff))

        self.log.debug("Landmarks %s" % landmarks)
        page.landmarks = landmarks
        return r,top_left_x,top_left_y,longdiff

    

    def is_tinted_by(triplet,diff):
        """ return True if triplet tint  >=diff
        
        For this purpose, tint is defined as the maximum absolute value
        of the difference between any two members of the triplet;
        tint (126,128,130) is 4 and tint (128,128,128) is 0.

        Triplet may be a pixel or may be a mean from ImageStat.Stat.
        CAUTION: "Black" may have a non-zero tint
        """
        tint0_1 = abs(triplet[0] - triplet[1])
        tint1_2 = abs(triplet[1] - triplet[2])
        tint0_2 = abs(triplet[0] - triplet[2])
        tint = max(max(tint0_1,tint1_2), tint0_2)
        return tint >= diff
        
    def get_ulc_if_tinted_oval(self,image,x,y):
        """Return upper left corner of oval bbox if x,y on oval's bottom wall.

        Look back to find trailing oval offering tint at:

        left wall, up by half oval height and back by half oval width,
        with half oval width of checking;

        right wall, up by half oval height and forward by half oval width,
        with half oval width of checking;

        and top wall, up by oval height with half oval height of checking.
        """
        left_wall = -1
        for test_x in range(x-(oval_width/2),x+(oval_width/2)):
            p = getpixel((test_x,y))
            if is_tinted_by(p,10):
                left_wall = test_x
                break
        right_wall = -1
        for test_x in range(x+(oval_width/2),x+oval_width):
            p = getpixel((test_x,y))
            if is_tinted_by(p,10):
                right_wall = test_x
                break
        top_wall = -1
        for test_y in range(y - (3*oval_height/2),y-(oval_height/2),1):
            p = getpixel((x,test_y))
            if is_tinted_by(p,10):
                top_wall = test_y
                break
        if left_wall >= 0 and right_wall >= 0 and top_wall >=0:
            return (left_wall,top_wall)
        else:
            return ()
        
    def find_tinted_voteops(self, page):
        """NOT IN USE:Given deskewed image and starting x, return list of tinted voteops.

        The Humboldt Diebold images are so compressed that the tint is iffy.
        So an alternative is to use a darkness test followed by a check for
        darkness at the correct related pixels, COUPLED WITH A TEST FOR 
        NO SUBSTANTIAL DARKNESS IN TEST ZONES OUTBOARD .04" to .05" 
        FROM THE OVAL.


        Scan down deskewed image at starting x.

        When tinted pixel found, call is_bottom_wall_of_oval to determine
        existence of vote oval ending at coords.

        Group into sublists by using untinted dark pixels as breaks.

        When only one oval is found in a sublist, 
        check for additional oval at same y offset

        """
        retlist = []
        # start with one sublist
        retlist.append([])
        image = page.image
        for y in range(const.dpi,
                       im.size[1]-const.dpi,
                       1):
            p = image.getpixel((starting_x,y))
            # on tinted pix, check for and append oval to current sublist;
            # on darkened untinted pix, add new sublist
            if is_tinted_by(p,10):
                ulc_of_oval = get_ulc_if_tinted_oval(image,starting_x,y)
                if len(ulc_of_oval)>1:
                    # you could OCR now and store Choices instead of coords
                    retlist[-1].append(ulc_of_oval)
            elif p[0]< const.line_darkness_threshold and len(retlist[-1]>0):
                # you could OCR from here to the next oval encountered
                # and store Contest rather than sublist
                retlist.append([])
        
        return retlist
                
    def get_layout_code(self, page):
        """
        From PILB:
static inline PyObject*
diebolddashcode(Imaging im, int max4dark, int dpi, int starty)
{
  UINT8 *p;
  int x,y;
  int xcontig = 0;
  int ycontig = 0;
  int startx = 0;
  int foundx = 0;
  int foundy = 0;
  int startlastx = 0;
  int foundlastx = 0;
  int foundlasty = 0;
  int eighth = dpi/8;
  float distance = 0.;
  INT32 accum = 0;
  int n;
  // look for (x,y) of first dash at extreme left of image 
  // starting at starty and continuing upwards for one inch;
  // a dash will consist of at least 1/8" of dark pixels repeated for three rows
  foundx = 0;
  xcontig = 0;
  for( y = starty; y > (starty - dpi); y--){
    //printf("y=%d, max4dark %d, starty %d dpi %d\n",y,max4dark, starty, dpi);
    // if we failed to reach the necessary thickness of potential dash,
    // reset the starting point to zero for subsequent lines
    if (xcontig < eighth){
      printf("Setting startx back to zero at %d\n",y);
      startx = 0;
    }
    xcontig = 0;
    for (x = startx; x < startx + dpi; x++){
      p = (UINT8*) &im->image32[y][x];
      if (*p <= max4dark){
	xcontig++;
	if (xcontig > eighth){
	  foundx = x - xcontig;
	  foundx++;
	  foundy = y;
	  ycontig++;
	  printf("%d on line %d makes %d\n",xcontig,y,ycontig);
	  break;
	}
      }
      else {
	xcontig = 0;
      }
    }
    if (foundx>0){
      startx = foundx;
      //printf("ycontig now %d, startx set to %d\n",ycontig,startx);
    }
    if (ycontig == dpi/32){ 
      //printf("Ycontig is %d at line %d, foundx is %d\n",ycontig, y,foundx);
      break;
    }
    // found a dash ending at foundx+xcontig, foundy - ycontig
  }
        """
        dash_height_pixels = adj(0.06)
        dash_width_pixels = adj(0.18)
        dash_window_width_pixels = adj(0.25)
        # page.landmarks:
        # inboard upper edges of extreme dashes at UL, UR, LR, LL
        # page.landmarks[2] is upper inboard coord of bottom right dash
        # page.landmarks[3] is upper inboard coord of bottom left dash
        # length available to page.landmarks is horiz dist between l2 and l3
        length = page.landmarks[2][0] - page.landmarks[3][0]
        start_y = page.landmarks[3][1] + (dash_height_pixels/2)
        end_y = page.landmarks[2][1] + (dash_height_pixels/2)
        # length should exclude the unmarked contents of the left dash's window
        length -= adj(0.07)
        # first code dash begins after those contents
        fcd_start_x = page.landmarks[3][0] + adj(0.07)
        # code dash centers are half dash widths
        fcd_center_x = fcd_start_x + (dash_width_pixels/2)
        
        # if the ballot width is not 8.5", save someone some trouble
        num_coding_dashes = 8 * 4
        calced_dashes = int(round(float(4*length)/const.dpi))
        if num_coding_dashes != calced_dashes:
            self.log.error("NCD %d calced %d" % (num_coding_dashes,calced_dashes))
            print "NCD %d calced %d" % (num_coding_dashes,calced_dashes)
            print page.landmarks[2][0] - page.landmarks[3][0]
            print length, length * 4, (length * 4.)/const.dpi
            print page.landmarks
            pdb.set_trace()

        # check 3x3 spots at center of each dash location for dark/light, 
        # build up a binary pattern corresponding to presence of dashes
        # beware of rounding errors as moving from dash window to dash window
        accum = 0
        for n in range(32):
            this_dash_center_x = fcd_center_x + int(round(n*length/32.))
            dist_from_start = this_dash_center_x - fcd_start_x
            dist_from_end = length - dist_from_start
            this_dash_center_y = int(round(
                ( (dist_from_start * end_y) + (dist_from_end * start_y) )
                /length)
            )
            # check 9 pix square at coord for avg red
            crop = page.image.crop(
                (this_dash_center_x - 1,
                 this_dash_center_y - 1,
                 this_dash_center_x + 2,
                 this_dash_center_y + 2))
            stat = ImageStat.Stat(crop)
            dark = (stat.mean[0] < const.line_darkness_threshold)
            self.log.debug("Intensity at (%d,%d) = %f; dark = %s" % (
                this_dash_center_x,
                this_dash_center_y,
                stat.mean[0],
                stat.mean[0] < const.line_darkness_threshold))
                                                 
            if dark:
                accum += 1
            accum *= 2
            self.log.debug( " Accum %x" % (accum,))
        return accum


    def build_front_layout(self, page):
        self.log.debug("Entering build front layout.")
        return self.build_layout(page)

    def build_back_layout(self, page):
        self.log.debug( "Entering build back layout.")
        return self.build_layout(page,back=True)

    def build_layout(self, page, back=False):
        """ Get layout and ocr information from Diebold ballot

        Assumes page.image has been deskewed.

        First, determine number of columns and starting x of each column.

        Initial pass dummies column starts by pre-filling column list at
        known offsets for 8.5" wide 3 column.

        Then, for each column:

        Get horizontal lines spanning column
        Horizontal lines separated by at least 1/2" may be a contest;
        within each potential contest, locate vote targets.

        Potential contests with more than one vote target may become
        contests appended to Contest list, the vote targets become choices
        on the Contest's choice list.

        Return list of contests.
        

        """
        thinline_width = adj(0.01)
        text_margin = adj(0.03)
        contest_list = []
        # columns begin 1/32" from inboard side of first dash,
        # and the first two columns of a three column Diebold ballot
        # are each 2.75" wide
        landmark_x = page.landmarks[0][0]
        
        column_bound_vlines = ( landmark_x + adj(.03),
                                landmark_x + adj(2.78),
                                landmark_x + adj(5.53),
                                landmark_x + adj(8.03) )
        # the last boundary vline is not a column start, only a column end
        column_start_vlines = column_bound_vlines[:-1]
        # the next column's start is the current column's end
        column_end_vlines = column_bound_vlines[1:]
        vthip = adj(const.vote_target_horiz_offset_inches)
        vt_width_pixels = adj(const.target_width_inches)
        for column_start_x, column_end_x in zip(column_start_vlines,
column_end_vlines):
            # add the config file vote offset to the column_x
            # to get the the start of a vote oval; add half the
            # oval width from the config file to get its center
            oval_center_x = column_start_x + vthip + (vt_width_pixels/2)
            oval_text_start_x = column_start_x + vthip + vt_width_pixels + text_margin
            # find horizontal lines searching at column center
            column_center_x = (column_start_x+column_end_x)/2

            lines = find_horizontal_lines(
                page, 
                column_center_x, 
                const.dpi)
            #print "Lines",lines, "at column center",column_center_x
            # find which pairs could be contests
            pot_contests = find_potential_contests(lines,const.dpi/2)
            #print "Potential Contests",pot_contests
            # find the vote targets between those pairs
            for contest_start_y, contest_end_y in pot_contests:
                self.log.debug("Searching targets from %d,%d to %d,%d" % (
                    column_start_x,contest_start_y, 
                    column_end_x,contest_end_y))
                vote_targets = find_untinted_voteops(page,
                                                     oval_center_x,
                                                     contest_start_y,
                                                     contest_end_y,
                                                     const.dpi)
                #print "Found vote targets at",vote_targets
                # if you've found any vote targets, 
                # create a contest and add vote_targets as choices
                                             
                if len(vote_targets)>0:
                    # ocr contest text
                    vertical_space_after_description = const.dpi/10
                    contest_text_croplist = (column_start_x + thinline_width,
                                             contest_start_y + thinline_width,
                                             column_end_x - thinline_width,
                                             vote_targets[0][1] - 
                                             vertical_space_after_description)
                    contest_text = self.extensions.ocr_engine(
                        page.image.crop(contest_text_croplist))
                    contest_text = self.extensions.ocr_cleaner(contest_text)
                    #pdb.set_trace()
                    this_contest = Ballot.Contest(
                        column_start_x,
                        contest_start_y,
                        column_end_x,
                        contest_end_y,
                        0,
                        contest_text)
                    #print "Appending",this_contest
                    #print contest_list
                    contest_list.append(this_contest)
                    # add vote targets
                    for n in range(len(vote_targets)):
                        this_target_x, this_target_y = vote_targets[n]
                        this_target_text_x = (this_target_x 
                                              + vt_width_pixels 
                                              + text_margin)
                        this_target_text_y = (this_target_y - text_margin)
                        try:
                            next_target_x, next_target_y = vote_targets[n+1]
                        except IndexError:
                            next_target_x = column_end_x - thinline_width
                            next_target_y = contest_end_y - thinline_width
                        if abs(next_target_x - this_target_x) > (const.dpi/4):
                            # the two targets bottom edges are aligned
                            choice_text_croplist = (
                                this_target_text_x,
                                this_target_text_y,
                                next_target_x - text_margin,
                                contest_end_y - thinline_width
                                )
                        else:
                            # the two targets left edges are aligned
                            choice_text_croplist = (
                                this_target_text_x,
                                this_target_text_y,
                                column_end_x - text_margin,
                                next_target_y - text_margin)
                        choice_text = self.extensions.ocr_engine(
                            page.image.crop(choice_text_croplist))
                        choice_text = self.extensions.ocr_cleaner(
                            choice_text)

                        this_choice = Ballot.Choice(
                            this_target_x,
                            this_target_y,
                            choice_text)
                        this_contest.choices.append(this_choice)
        return contest_list

