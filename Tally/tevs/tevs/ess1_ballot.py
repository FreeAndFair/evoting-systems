# ess1_ballot.py implements the Ballot interface 
# in Ballot.py for ballots following the style used in 
# Champaign County, IL. 
# Please see the file README_ESS.txt for details.
# The Trachtenberg Election Verification System (TEVS)
# is copyright 2009, 2010 by Mitch Trachtenberg 
# and is licensed under the GNU General Public License version 2.
# (see LICENSE file for details.)
"""
300dpi, 3 columns
Fronts
+ target at 134,100 (1/2" x 1/3")
+ target at 2380,88 (8" x 1/3")
+ target at 2398,4114 (8" x 13 2/3")
+ target at 154,4116 (1/2" x 13 2/3")
Black timing mark at (x1,y1)=(58,216),(x2,y2)=(282,262), 1/6" high x 2/3" wide
Outer bounding box begins 318,212, horizontally 0.6" from +, .36" below
right edge 2386,206, very slightly to right of +, .36" below
Next black box begins 1/2" below start of first black box
Subsequent black boxes begin at 1/3" intervals and are 1/6" tall
Left column boxes are 1/4" wide
Second column boxes either start 1/4" after end of first, and add 1/4"
or start .3" after end of first and add 2/15" (.13") 

Back + (158,94)  (2402,102) (2398,4132)  (154,4126)
Back box (134,208) (2204,218) (2196,4072) (132, 4062)
45 degree cut mark representing half of 1/2" box at left top

Row headers and row footers aligned with top and bottom black marks,
begin 0.1" after, roughly 0.125" whitish, 1/4" black, .125" whitish

Column lines .01"

Jurisdiction white on black
Contest black on gray or black on white
Text, if black on white, appears above vote ops but may optionally appear
below last vote op set.

Vote ops start 4/30" in from column edge, extend just under .25" and .125" tall and spaced 1/3" top to top.

Reliably show at least .05" continuous dark pixels at top and bottom center
"""


import Ballot
import const
from adjust import rotator
from cropstats import cropstats
from find_line import find_line
import Image, ImageStat
import math
import ocr
import pdb
import sys
from demo_utils import *

def adj(a):
    return int(round(float(const.dpi) * a))

def elim_halftone(x):
    if x>64:
        retval = 255
    else:
        retval = 0
    return retval

def oval_pattern(im,height,width,text_offset):
    """an empty oval will return True, otherwise False"""
    left_ok = False
    right_ok = False
    center_ok = True
    beyond_ok = True
    slip = adj(0.02)
    dark_threshold = 192
    vdark_threshold = 128
    try:
        for x in range(slip):
            for y in range(height):
                p = im.getpixel((x,y))
                if p[0]<dark_threshold: 
                    left_ok = True
                    break
        for x in range(width-slip,width+slip):
            for y in range(height):
                p = im.getpixel((x,y))
                if p[0]<dark_threshold: 
                    right_ok = True
                    break
        for x in range(width+slip,text_offset-slip):
            for y in range(height):
                p = im.getpixel((x,y))
                if p[0]<vdark_threshold:
                    beyond_ok = False
                    break
        # assumes oval is at or very near top of im
        for y in range(height/2-1,height/2+1):
            p = im.getpixel((width/2,y))
            if p[0]<vdark_threshold:
                center_ok = False
    except IndexError:
        return False

    return (left_ok and right_ok and beyond_ok and center_ok)

class Ess1Ballot(Ballot.Ballot):
    """Class representing ESS duplex ballots (or single-sided).

    The file name ess1_ballot.py and the class name EssBallot
    correspond to the brand entry in tevs.cfg (ess.cfg), 
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
        self.writein_xoff = adj(const.writein_zone_horiz_offset_inches)
        self.writein_yoff = adj(const.writein_zone_vert_offset_inches)
        self.writein_width = adj(const.writein_zone_width_inches)
        self.writein_height = adj(const.writein_zone_height_inches)
        self.allowed_corner_black = adj(const.allowed_corner_black_inches)
        self.back_upper_right_plus_x = 0
        self.back_upper_right_plus_y = 0
        super(Ess1Ballot, self).__init__(images, extensions)

    def extract_VOP(self, page, rotatefunc, scale, choice):
        """Extract a single oval, or writein box, from the specified ballot"""
        iround = lambda x: int(round(x))
        x, y = choice.coords()
        printed_oval_height = adj(const.target_height_inches)


        #BEGIN SHARABLE
        scaled_page_offset_x = page.xoff/scale
        scaled_page_offset_y = page.yoff/scale
        self.log.debug("Incoming coords (%d,%d), \
page offsets (%d,%d) scaled page offsets (%d,%d), template offsets (%d,%d)" % (
                x,y,
                page.xoff,page.yoff,
                scaled_page_offset_x,scaled_page_offset_y,
                page.template.xoff,page.template.yoff))
        # adjust x and y for the shift of landmark between template and ballot
        x = iround(x + scaled_page_offset_x - page.template.xoff)
        y = iround(y + scaled_page_offset_y - page.template.yoff)
        self.log.debug("Result of translation: (%d,%d)" % (x,y))
        
        x, y = rotatefunc(x, y, scale)
        self.log.debug("Result of rotation: (%d,%d)" % (x,y))
        # Below is using the pure python cropstats:
        cropx, cropy = x, y #not adjusted like in PILB cropstats

        crop = page.image.crop((
            cropx - page.margin_width,
            cropy - page.margin_height,
            min(cropx + page.margin_width + page.target_width,
                page.image.size[0]-1),
            min(cropy + page.margin_height + page.target_height,
                page.image.size[1]-1)
        ))

        # Commenting out material below as regardless of adding or subtracting
        # based upon it, it makes things worse in some situations (?)
        # The rotation is working well to capture the correct area.
        
        """
        # check strip at center to look for either filled or empty oval;
        # recenter vertically

        stripe = crop.crop(((crop.size[0]/2),0,(crop.size[0]/2)+1,crop.size[1]-1))
        before_oval = 0
        after_oval = 0
        oval = 0
        dark_threshold = 192
        stripedata = list(stripe.getdata())
        for num,p in enumerate(stripedata):
            if p[0] > dark_threshold:
                before_oval += 1
            else:
                try:
                    if ((stripedata[before_oval+printed_oval_height-2][0] < dark_threshold) or 
                        (stripedata[before_oval+printed_oval_height-1][0] < dark_threshold) or 
                        (stripedata[before_oval+printed_oval_height][0] < dark_threshold) or
                        (stripedata[before_oval+printed_oval_height+1][0] < dark_threshold) or
                        (stripedata[before_oval+printed_oval_height+2][0] < dark_threshold)):
                        oval_start = num
                        ov_end = num + printed_oval_height
                        after_oval = stripe.size[1] - (oval_start+printed_oval_height)
                        break
                except IndexError:
                    break
        afterlessbefore = int(round((after_oval - before_oval)/2))
        if abs(afterlessbefore)>2:
            cropy += afterlessbefore
            self.log.debug("Result of afterlessbefore %d: (%d,%d)" % (
                    afterlessbefore,x,cropy))
            crop = page.image.crop((
                cropx - page.margin_width,
                cropy - page.margin_height,
                min(cropx + page.margin_width + page.target_width,
                    page.image.size[0]-1),
                min(cropy + page.margin_height + page.target_height,
                    page.image.size[1]-1)
                ))
        """
        stats = Ballot.IStats(cropstats(crop, x, y))

        voted, ambiguous = self.extensions.IsVoted(crop, stats, choice)
        writein = self.extensions.IsWriteIn(crop, stats, choice)
        if writein:
            crop = page.image.crop((
                 cropx - page.margin_width + self.writein_xoff,
                 cropy - page.margin_height + self.writein_yoff,
                 min(cropx + page.margin_width + self.writein_width,
                     page.image.size[0]-1),
                 min(cropy + page.margin_height + self.writein_height,
                     page.image.size[1]-1)
            ))

        return cropx, cropy, stats, crop, voted, writein, ambiguous

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
        return self.find_front_landmarks(page)

    def find_front_landmarks(self, page):
        """find the left and right corners of the uppermost line"""
        iround = lambda a: int(round(float(a)))
        width = adj(0.75)
        height = adj(0.75)
        # for testing, fall back to image argument if can't get from page
        try:
            im = page.image
        except:
            im = page

        # generate ulc, urc, lrc, llc coordinate pairs
        landmarks = []

        # use corners of top and bottom lines in preference to circled-plus
        # as the circled plus are often missed due to clogging, etc...
        try:
            a,b,c,d = find_line(im,im.size[0]/2,100,
                                threshold=64,black_sufficient=True)
            self.log.debug("Top line coords (%d,%d)(%d,%d)" % (a,b,c,d))
        except Exception:
            pass
        else:
            landmarks.append([a,b])
            landmarks.append([c,d])

        try:
            # changing search start from 1/3" above bottom to 1/14" above
            a,b,c,d = find_line(im,im.size[0]/2,im.size[1]-adj(0.07),-adj(0.75),
                                threshold=64,black_sufficient=True)
            self.log.debug("Top line coords (%d,%d)(%d,%d)" % (a,b,c,d))
        except Exception:
            pass
        else:
            landmarks.append([c,d])
            landmarks.append([a,b])

        try:
            x,y = landmarks[0][0],landmarks[0][1]
            longdiff_a = landmarks[3][1] - landmarks[0][1]
            shortdiff_a = landmarks[3][0] - landmarks[0][0]
            hypot = math.sqrt(longdiff_a*longdiff_a + shortdiff_a*shortdiff_a)
            r_a = float(shortdiff_a)/float(longdiff_a)
            longdiff_b = landmarks[1][0] - landmarks[0][0]
            shortdiff_b = landmarks[0][1] - landmarks[1][1]
            hypot = math.sqrt(longdiff_b*longdiff_b + shortdiff_b*shortdiff_b)
            r_b = float(shortdiff_b)/float(longdiff_b)
            magnitude_r = min(abs(r_a),abs(r_b))
            if r_a < 0. and r_b < 0.:
                sign_r = -1
            else:
                sign_r = 1
            r = magnitude_r * sign_r
        except IndexError:
            # page without landmarks; if this is a back page, it's ok
            raise Ballot.BallotException

        if abs(r) > 0.1: 
            self.log.debug("Tangent is unreasonably high, at %f." % (r,))
            print "Tangent is unreasonably high, at %f." % (r,)
            #pdb.set_trace()
        # we depend on back landmarks being processed after front
        self.back_upper_right_plus_x = landmarks[1][0]
        self.back_upper_right_plus_y = landmarks[1][1]
        self.log.debug("landmarks %s,rot %f,(%d,%d)" % (landmarks,r,x,y))
        page.landmarks = landmarks
        return r,x,y,hypot
    
    def get_party_id(self, page):
        """ get party id by ocr'ing ballot"""
        return "No party id."

    def get_precinct_id(self, page):
        """ get precinct id by ocr'ing ballot"""
        sixth = adj(1./6.)
        half = adj(1/2.)
        try:
            precinct = page.image.crop((page.landmarks[3][0] + half,
                                        page.landmarks[3][1] - sixth,
                                        page.landmarks[3][0] + adj(2),
                                        page.landmarks[3][1] ))
            precinct.save("/tmp/precinct.jpg")
            precincttext = ocr.tesseract(precinct)
            precincttext = ocr.clean_ocr_text(precincttext)
            precincttext = precincttext.strip()
            precincttext = precincttext.replace("\n","//").strip()
        except IndexError:
            precincttext = "?"
        return precincttext


    def get_layout_code(self, page):
        """ Determine the layout code by inspecting the left edge 

        The layout code must be determined on a vendor specific basis;
        it is usually a series of dashes or a bar code at a particular
        location on the ballot.

        Layout codes may appear on both sides of the ballot, or only
        on the fronts.  If the codes appear only on the front, you can
        file the back layout under a layout code generated from the
        front's layout code.
        If using circled plus,
        # if front, starting point is 1/4" before plus horizontal offset,
        # and .36" below plus vertical offset
        front_adj_x = adj(-0.25)
        front_adj_y = adj(0.36)
        But, we are using left corner of top line
        """
        # if we already have a barcode for the front,
        # we'll prepend back to that and use that as our "back barcode"
        if len(page.ballot.pages[0].barcode) > len(page.barcode):
            return "Back%s" % (page.ballot.pages[0].barcode)
        front_adj_x = adj(-0.86)
        front_adj_y = adj(0.)
        # if the upper left corner of the line is so far to the left
        # that we'd be off the page looking for timing marks on the
        # left, this is a back and we will not find a bar code
        if (page.xoff + front_adj_x) < 0:
            return "Back%s" % (page.ballot.pages[0].barcode)
        barcode,tm = barcode_and_timing_marks(
            page.image,
            page.xoff + front_adj_x,
            page.yoff + front_adj_y,
            const.dpi)
                                  
        return barcode

    def build_front_layout(self, page):
        self.log.debug("Entering build front layout.")
        return self.build_layout(page)

    def build_back_layout(self, page):
        self.log.debug( "Entering build back layout.")
        return self.build_layout(page,back=True)

    def get_left_edge_zones(self, page, column_x):
        """ return a set of pairs, (y_value, letter) for zone starts"""
        letters = []
        left = column_x + adj(0.03)
        right = left + adj(0.03)
        im = page.image
        stripe = im.crop((left,0,right,im.size[1]-1))
        lastletter = "W"
        lastred = 255
        lastdarkest = 255
        for y in range(stripe.size[1]-(const.dpi/2)):
            crop = stripe.crop((0,y,1,y+(const.dpi/32)))
            stat = ImageStat.Stat(crop)
            red = stat.mean[0]
            darkest = stat.extrema[0][0]
            if (red < 32) and (darkest < 32) and (lastred >= 32):
                if lastletter <> "B":
                    if lastletter == "G" and letters[-1][0]>(y-adj(0.1)):
                        letters = letters[:-1]
                    letters.append((y,"B"))
                    lastletter = "B"
            elif red >= 32 and red < 240 and darkest < 224:
                if lastletter <> "G":
                    letters.append((y,"G"))
                    lastletter = "G"
            elif red >=240:
                if lastletter <> "W":
                    if lastletter == "G" and letters[-1][0]>(y-adj(0.1)):
                        letters = letters[:-1]
                    letters.append((y,"W"))
                    lastletter = "W"
            lastred = red
            lastdarkest = darkest
        self.log.debug("Left edge zones: %s" % (letters,))
        return letters

    def get_middle_zones(self, page, column_x):
        """ return a set of pairs, (y_value, letter) for zone starts"""
        letters = []
        left = column_x
        right = left + adj(0.5)
        im = page.image
        stripe = im.crop((left,0,right,im.size[1]-1))
        lastletter = "W"
        lastred = 255
        lastdarkest = 255
        for y in range(stripe.size[1]-(const.dpi/2)):
            crop = stripe.crop((0,y,1,y+(const.dpi/4)))
            stat = ImageStat.Stat(crop)
            red = stat.mean[0]
            darkest = stat.extrema[0][0]
            if (darkest < 128) and lastletter == "W":
                letters.append((y+(const.dpi/4),"B"))
                lastletter = "B"
            elif (darkest >= 128) and lastletter == "B":
                letters.append((y,"W"))
                lastletter = "W"
        return letters

    def generate_transition_list_from_lines(self,image,regionlist,column_bounds,lines):
        """given a set of horizontal split lines, gen contests from column"""
        ccontest_default = "No current contest"
        ccontest = ccontest_default
        cjurisdiction_default = "No current jurisdiction"
        cjurisdiction = cjurisdiction_default
        contest_instance = None
        for n in range(len(lines)):
            this_y = lines[n][1]
            try:
                next_y = lines[n+1][1]
            except IndexError:
                next_y = image.size[1]-1
            self.get_title_and_votes_from(image,regionlist,
                                          (column_bounds[0],
                                           this_y,
                                           column_bounds[1],
                                           next_y))
            self.log.debug( "Retrieve title and votes in zone  %d,%d to %d,%d" % (column_bounds[0],this_y,column_bounds[1],next_y))
        # filter regionlist to contain only contests with choices
        # set jurisdiction based on previous rejected "contest"
        rejectedlist = [x for x in regionlist if len(x.choices)==0]
        #print "Rejections",[x.description for x in rejectedlist]
        regionlist = [x for x in regionlist if len(x.choices)>0]
        return regionlist

    def generate_transition_list_from_zones(self,image,regionlist,column_bounds,left,middle):
        """ given the pair of zone lists, generate a comprehensive list

        We should then be able to merge these sets of split information:
        anything where we find solid black or halftone is a definite break
        which may be followed either by another black or halftone area, by
        a description area, or by a vote area.
        """
        ccontest_default = "No current contest"
        ccontest = ccontest_default
        cjurisdiction_default = "No current jurisdiction"
        cjurisdiction = cjurisdiction_default
        contest_instance = None
        for n in range(len(left)):
            this_y = left[n][0]
            try:
                next_zone = left[n+1]
            except IndexError:
                next_zone = [0,'X']
            next_y = next_zone[0]
            rel_end = next_y - (const.dpi/10)
            if left[n][1]=='B' or left[n][1]=='G':
                self.log.debug("%s zone at %d to %d %s" % (left[n][1],
                                                           this_y,
                                                           next_y,
                                                           next_zone))
                # if it's a legitimage gray zone and the next zone is white,
                # that white zone is a voting area (or empty)
                if (next_y - this_y) > (const.dpi/4):
                    crop = image.crop((column_bounds[0],
                                       this_y,
                                       column_bounds[1],
                                       next_y))
                    crop = Image.eval(crop,elim_halftone)
                    cjurisdiction = ocr.tesseract(crop)
                    cjurisdiction = cjurisdiction.replace("\n","//").strip()
                    self.log.debug( "Jurisdiction %s" % (cjurisdiction,))
                    cjurisdiction = ocr.clean_ocr_text(cjurisdiction)
                    self.log.debug( "Cleaned Jurisdiction %s" % (cjurisdiction,))
            if left[n][1]=='W':
                self.get_title_and_votes_from(image,regionlist,
                                         (column_bounds[0],
                                          this_y,
                                          column_bounds[1],
                                          next_y))
                self.log.debug( "White zone at %d to %d %s" % (this_y,next_y,next_zone))
        # filter regionlist to contain only contests with choices
        regionlist = [x for x in regionlist if len(x.choices)>0]
        return regionlist

    def get_dark_zones(self,crop,dark_intensity=192):
        """ return starting and ending y offsets of dark areas in crop"""
        in_dark = False
        dark_zones = []
        dark_start = 0
        dark_end = 0
        for y in range(crop.size[1]-1):
            linecrop = crop.crop((const.dpi/10,
                                  y,
                                  crop.size[0] - (const.dpi/10),
                                  y+1))
            linestat = ImageStat.Stat(linecrop)
            if (linestat.extrema[0][0] < dark_intensity) and not in_dark:
                in_dark = True
                dark_start = y
            elif (linestat.extrema[0][0] >= dark_intensity) and in_dark:
                in_dark = False
                dark_end = y
                dark_zones.append([dark_start,dark_end])
        return dark_zones

    def get_contests_and_votes_from(self,image,regionlist,croplist):
        """ given an area known to contain votes and desc text, return info

        The cropped area will contain contest descriptions and voting areas.
        Unfortunately, the contest descriptions are not indented away from
        the oval voting areas.  So...  we crop looking for white line splits,
        and then treat every line as either part of a contest or as a vote
        line, depending on whether we find a pattern of white indicating
        the line contains only an oval and a single word, YES or NO.
        """
        ov_off = adj(const.vote_target_horiz_offset_inches)
        ov_end = ov_off + adj(const.target_width_inches)

        txt_off = adj(const.candidate_text_horiz_offset_inches)

        contests = []
        contest_string = ""
        crop = image.crop(croplist)
        # indent by 1/10" to avoid edges, then crop single pixel lines,
        # finding beginning and end of zones which include dark pixels
        # now check each dark zone to see if it is a vote op 
        # or if it is descriptive text; vote ops will have an oval
        # in the oval channel beginning at ov_off
        # and extending until ov_end
        dark_zones = self.get_dark_zones(crop,dark_intensity=160)
        contest_created = False
        for dz in dark_zones:
            zonecrop1 = crop.crop((const.dpi/10,
                                    dz[0],
                                    crop.size[0]-(const.dpi/10), 
                                    dz[1]))
            zonecrop2 = crop.crop((ov_end,
                                    dz[0],
                                    txt_off, 
                                    dz[1]))
            zone2stat = ImageStat.Stat(zonecrop2)
            zonecrop3 = crop.crop((txt_off,
                                    dz[0],
                                    txt_off + const.dpi,
                                    dz[1]))
            zone1text = ocr.tesseract(zonecrop1)
            zone1text = ocr.clean_ocr_text(zone1text)
            zone3text = ocr.tesseract(zonecrop3)
            zone3text = ocr.clean_ocr_text(zone3text)
            intensity_suggests_voteop = False
            length_suggests_voteop = False
            if zone2stat.mean[0]>244: intensity_suggests_voteop = True
            if len(zone3text)<6: length_suggests_voteop = True
            if not intensity_suggests_voteop and not length_suggests_voteop:
                contest_created = False
                contest_string += zone1text.replace("\n","/")
            elif intensity_suggests_voteop and length_suggests_voteop:
                # create contest if none created, then
                if not contest_created:
                    contest_created = True
                    self.log.debug("Creating contest %s" % (contest_string,))
                    regionlist.append(Ballot.Contest(croplist[0],
                                                     croplist[1]+dz[0],
                                                     croplist[2],
                                                     croplist[1]+dz[1],
                                                     0,
                                                     contest_string))
                    contest_string = ""
                # add voteop to contest
                choice_string = zone3text
                self.log.debug("Adding choice %s" % (choice_string,))
                regionlist[-1].append(
                    Ballot.Choice(
                        croplist[0]+ov_off,
                        croplist[1]+ dz[0],
                        choice_string
                        )
                    )

            else:
                if contest_created:
                    contest_string += zone1text.replace("\n","//")
                else:
                    self.log.debug( "Problem determining whether contest or choice")
                    self.log.debug("Gap mean values %s" % (zone2stat.mean,))
                    self.log.debug("Zone3 text %s" % (zone3text,))
                    self.log.debug("Contest string: %s" % (contest_string,))
        return dark_zones

    def get_title_and_votes_from(self,image,regionlist,croplist,last_title="NO TITLE"):
        """ given an area known to contain contest title and votes, return info

        The cropped area will contain a title area at the top, 
        followed by voting areas.  Voting areas will
        contain ovals in the oval column.  Descriptive text to the right of
        the ovals will be assigned to each oval based on being at or below
        the oval.

        """
        ov_off = adj(const.vote_target_horiz_offset_inches)
        ov_ht = adj(const.target_height_inches)
        ov_wd = adj(const.target_width_inches)
        ov_end = ov_off + ov_wd
        txt_off = adj(const.candidate_text_horiz_offset_inches)


        choices = []
        crop = image.crop(croplist)
        if croplist[2]==0 or croplist[3]==0:
            return []

        dark_zones = self.get_dark_zones(crop)

        next_dark_zones = dark_zones[1:]
        next_dark_zones.append([crop.size[1]-2,crop.size[1]-1])
        skipcount = 0


        # for each dark zone, determine the first dark x
        encountered_oval = False
        dzstyle = []
        for dz in dark_zones:
            # crop each dark strip
            # losing the area to the left of the possible vote target
            # and an equivalent area on the right
            dzcrop = crop.crop((ov_off,
                                dz[0],
                                crop.size[0]-ov_off,
                                dz[1]))

            firstx = dzcrop.size[0]
            lastx = 0
            for y in range(dzcrop.size[1]):
                for x in range(dzcrop.size[0]):
                    p0 = dzcrop.getpixel((x,y))
                    if p0[0] < 192:
                        firstx = min(firstx,x)
                        lastx = max(lastx,x)
            lastxindent = dzcrop.size[0]-lastx

            # unfortunately, it is hard to tell a filled oval from a title
            # that begins about the same x offset as ovals; we will
            # recognize that titles come first and are symmetric
            # ovals start at a defined offset and will have a minimum height
            # and, if empty, will match a particular dark/light pattern
            symmetric = (abs(firstx-lastxindent) < adj(0.05))
            tall_enough = (dz[1]-dz[0] >= int(ov_ht * .8))

            ov_pat = oval_pattern(dzcrop,ov_ht,ov_wd,txt_off-ov_off)

            if not encountered_oval and not ov_pat:
                dzstyle.append("T")

            elif tall_enough and firstx <= adj(0.02):
                dzstyle.append("V")
                encountered_oval = True

            elif ((firstx >= (txt_off - ov_off - adj(0.02))) and not tall_enough):
                dzstyle.append("W")
            else:
                dzstyle.append("-")


        contest_instance = None
        choice = None
        title_array = []
        contest_created = False
        for index,style in enumerate(dzstyle):
            if style=="T":
                titlezone = crop.crop((adj(0.1),
                                      dark_zones[index][0],
                                      crop.size[0]-adj(0.1),
                                      dark_zones[index][1]))
                zonetext = ocr.tesseract(titlezone)
                zonetext = ocr.clean_ocr_text(zonetext)
                zonetext = zonetext.strip()
                zonetext = zonetext.replace("\n","//").strip()
                title_array.append(zonetext)
            elif style=="V":
                if title_array is not None:
                    zonetext = "/".join(title_array)
                    title_array = None
                    if len(zonetext) < 4:zonetext = last_title
                    contest_instance = Ballot.Contest(croplist[0], 
                                                  croplist[1],
                                                  croplist[2],
                                                  croplist[3], 
                                                  0,
                                                  zonetext[:80])
                    contest_created = True
                    regionlist.append(contest_instance)
                if not contest_created:
                    print "WARNING: Choice but no contest."
                    pdb.set_trace()
                    continue
                choicezone = crop.crop((txt_off,
                                      dark_zones[index][0],
                                      crop.size[0]-adj(0.1),
                                      dark_zones[index][1]))
                zonetext = ocr.tesseract(choicezone)
                zonetext = ocr.clean_ocr_text(zonetext)
                zonetext = zonetext.strip()
                zonetext = zonetext.replace("\n","//").strip()

                # find the y at which the actual oval begins 
                # which may be lower than the dark_zone start
                choice_y = dark_zones[index][0]

                # Look up to 0.2 inches beneath beginning of dark zone
                # for an oval darkening the oval region
                contig = 0
                for adj_y in range(adj(0.2)):
                    ovalcrop = crop.crop((ov_off,
                                          choice_y+adj_y,
                                          ov_end,
                                          choice_y+adj_y+1))
                    ovalstat = ImageStat.Stat(ovalcrop)
                    if ovalstat.extrema[0][0] < 240:
                        contig += 1
                        if contig > adj(0.03):
                            choice_y += (adj_y-adj(0.03))
                            found = True
                            break
                    else:
                        contig = 0

                choice = Ballot.Choice(croplist[0]+ov_off, 
                                       croplist[1]+choice_y, 
                                       zonetext)
                contest_instance.append(choice)
                #if zonetext.startswith("Randy"):
                #    print "Randy"
                #    pdb.set_trace()
                #    print "Randy"
            elif style=="W" and len(dzstyle)>(index+1) and dzstyle[index+1] in "W-":
                if title_array is not None:
                    title_array = None

                try:
                    choice.description = "Writein"
                except:
                    pass
        return regionlist

    def build_layout(self, page, back=False):
        """ get layout and ocr information from ess ballot
    The column markers represent the vote oval x offsets.
    The columns actually begin .14" before.
    We search the strip between the column edge and the vote ovals,
    looking for intensity changes that represent region breaks
    such as Jurisdiction and Contest changes.

    Unfortunately, there may be a full-ballot-width column at the top,
    containing instructions.  Random text in the instructions will trigger
    various false region breaks.

    More unfortunately, there is an inconsistency in the way jurisdictions
    and contests are handled.  (It looks good to humans.)

    Contests may begin with a black text on grey header (generally 
    following Jurisdictions as white text on black.  Contests with only
    Yes and No choices begin with black text on white background, and
    may precede either a white text on black zone OR another contest.

    The contest titles are hard to differentiate from contest descriptions,
    which can be lengthy.

    Finally, contest descriptions can continue BELOW the voting area
    of the contest.

    We make one necessary assumption, and that is that the vote area in
    such YES/NO contests will have text extending no more than halfway
    into the column, while any text will extend, except for its last line,
    more than halfway into the column.

    We'll take a vertical stripe beginning at the column center and
    of width 1/2", and look for the presence of black or gray pixels 
    in zones 1/4" tall, enough to span one and a half text lines.
    This should allow us to capture continuous vertical stretches of text
    without repeatedly finding "text", "no text".

    We'll take another vertical stripe at the very start of the column,
    from .03" for .03".  This is the extreme margin, and should allow us
    to capture zones with black headlines and grey backgrounds.  Halftoned
    areas are tricky -- they may contain no pixels more than half dark.

    We'll test for pixels of 224 or below, and an average intensity over
    a block of 240 or below.

    We should then be able to merge these sets of split information:
    anything where we find solid black or halftone is a definite break
    which may be followed either by another black or halftone area, by
    a description area, or by a vote area.

    Black, gray, and white zones are located by reading the thin margin strip.
    They must be stored in such a way that there preceding zone color is
    also available.  If the preceding zone color is gray, the white zone
    is a Vote zone.  If the preceding color zone is black, the white zone
    will contain Descriptions and YesNoVote zones.
    White zones can be analyzed by the thick center strip, combined
    with the last reading.  Where the white zone follows gray 
    center strip has text, the white zone is a Description, where the
    center strip has no text, the white zone is a YesNoVote zone.

    The five types of zones (Black, Desc, Vote1, YesNoVote, Gray) will have the
    following possible sequences.

    B -> G,D,V (capture black as Jurisdiction AND Contest)

    G -> D,V (capture G as Contest)

    D -> V,Y,B (capture D as Contest)
           
    V -> B,D (capture V as sequence of votes for current Contest)
    
    Y -> B,D (capture Y as sequence of votes for current Contest)

    When we find a vote area, it will be followed by a black or gray 
    divider or by a new description area.

    Description areas may likewise be followed by vote areas or black or gray.

    in unbroken regions, any areas with their right halves empty 
    will be presumed to represent either blank areas or voting locations.

        """
        ov_off = adj(const.vote_target_horiz_offset_inches)
        self.log.debug( "Entering build_layout.")

        regionlist = []
        n = 0
        # column_markers returns a location 0.14" into the column
        ref_pt = [0,0]
        ref_pt[0] = page.xoff + 2
        ref_pt[1] = page.yoff - 2
        if back:
            ref_pt[0] = page.landmarks[1][0]
            ref_pt[1] = page.landmarks[1][1] - 2
            self.log.debug( "Building BACK layout" )
        self.log.debug("Reference point: %s" % ( ref_pt,))

        columns = column_markers(page)
        try:
            column_width = columns[1][0] - columns[0][0]
        except IndexError:
            column_width = page.image.size[0] - const.dpi
        regionlist = []
        for cnum, column in enumerate(columns):
            column_x = column[0] - ov_off
            # determine the zones at two offsets into the column
            left_edge_zones = self.get_left_edge_zones(page,column_x)
            middle_zones = self.get_middle_zones(page,column_x+(column_width/2))
            # find solid lines in column XXX
            a,b,c,d = 0,0,0,0
            column_crop = page.image.crop((column_x,
                                           0,
                                           column_x + column_width,
                                           page.image.size[1] - adj(0.5)
                    ))
            column_crop.save("/tmp/column_crop.jpg")
            try:
                horizontal_lines = []
                advance_y_by = page.landmarks[0][1]
                last_y_offset = 0
                while True:
                    l = find_line(column_crop,starty = advance_y_by,threshold=64)
                    if l is None:
                        a = 0
                        b = 0 
                        c = 0
                        d = 0
                        advance_y_by += 300
                    else:
                        a = l[0]
                        b = l[1]
                        c = l[2]
                        d = l[3]
                        advance_y_by = (b + adj(0.1))
                    # grab lines that extend across 90% of column width
                    if a < adj(0.06) and c > int(column_crop.size[0]*.9):
                        horizontal_lines.append(l)
                        self.log.debug("Found line, %s %d %d %d %d" % (column_x,a,b,c,d))
                        contest_crop = column_crop.crop((0,
                                          last_y_offset,
                                          column_crop.size[0]-1,
                                          b))
                        contest_crop.save("/tmp/contest_crop_%d_%d.jpg" % (column_x,last_y_offset))
                        last_y_offset = b
                    if advance_y_by >= (page.image.size[1] - adj(0.5)):
                        break
            except Exception,e:
                print e
                pdb.set_trace()
            
            self.log.debug("Column %d at x offset %d" % (cnum,column_x))
            self.log.debug("Lines within column %s" % (horizontal_lines,))
            self.generate_transition_list_from_lines(
                page.image,
                regionlist,
                (column_x,
                column_x+column_width),
                horizontal_lines)
            """self.generate_transition_list_from_zones(
                page.image,
                regionlist,
                (column_x,
                column_x+column_width),
                left_edge_zones,
                middle_zones
                )"""
        return regionlist

def adjust_ulc(image,left_x,top_y,max_adjust=5):
    """ brute force adjustment to locate precise b/w boundary corner"""
    target_intensity = 255
    gray50pct = 128
    gray25pct = 64
    orig_adj = max_adjust
    while max_adjust > 0 and target_intensity > gray50pct:
        max_adjust -= 1
        left_target_intensity = image.getpixel((left_x-2,top_y))[0]
        target_intensity = image.getpixel((left_x,top_y))[0]
        right_target_intensity = image.getpixel((left_x+2,top_y))[0]
        above_target_intensity = image.getpixel((left_x,top_y-2))[0]
        above_right_target_intensity = image.getpixel((left_x+2,top_y-2))[0]
        above_left_target_intensity = image.getpixel((left_x-2,top_y-2))[0]
        below_target_intensity = image.getpixel((left_x,top_y+2))[0]
        below_left_target_intensity = image.getpixel((left_x-2,top_y+2))[0]
        below_right_target_intensity = image.getpixel((left_x+2,top_y+2))[0]
        changed = False
        if below_target_intensity > gray25pct and target_intensity > gray25pct:
            left_x += 2
            changed = True
        elif below_left_target_intensity <= gray50pct:
            left_x -= 2
            changed = True
        if right_target_intensity > gray25pct and target_intensity > gray25pct:
            top_y += 2
            changed = True
        elif above_right_target_intensity <= 127:
            top_y -= 2
            changed = True
        if not changed:
            break
    if max_adjust == 0 and changed == True:
        e = "could not fine adj edge at (%d, %d) after %d moves" % (left_x,
                                                                    top_y,
                                                                    orig_adj)
        raise Ballot.BallotException, e
    return (left_x,top_y)

def barcode_and_timing_marks(image,x,y,dpi=300):
    """locate timing marks and code, starting from closest to line edge"""
    #"""locate timing marks and code, starting from closest to ulc symbol"""
    # go out from + towards left edge by 1/8", whichever is closer
    # down from + target to first dark, then left to first white
    # and right to last white, allowing a pixel of "tilt"


    retlist = []
    tenth = adj(0.1)
    half = adj(0.5)
    third = adj(0.33)
    qtr = adj(0.25)
    down = adj(0.33)
    sixth = adj(0.167)
    twelfth = adj(0.083)
    gray50pct = 128


    left_x = x
    top_y = y
    retlist.append( (left_x,top_y) )
    # now go down 1/2" and find next ulc, checking for drift
    top_y += half
    for n in range(tenth):
        pix = image.getpixel((left_x+tenth,top_y))
        if pix[0] > 128:
            top_y = top_y + 1

    code_string = ""
    zero_block_count = 0
    while True:
        if top_y > (image.size[1] - const.dpi):
            break
        (left_x,top_y) = adjust_ulc(image,left_x,top_y)
        # check for large or small block to side of timing mark
        block = block_type(image,qtr,left_x+half,top_y+twelfth)
        if block==0: 
            zero_block_count += 1
        elif block==1:
            code_string = "%s%dA" % (code_string,zero_block_count)
            zero_block_count = 0
        elif block==2:
            code_string = "%s%dB" % (code_string,zero_block_count)
            zero_block_count = 0
            
        retlist.append((left_x,top_y))
        # now go down repeated 1/3" and find next ulc's until miss
        top_y += third
    # try finding the last at 1/2" top to top
    left_x = retlist[-1][0]
    top_y = retlist[-1][1]
    top_y += half
    (left_x,top_y) = adjust_ulc(image,left_x,top_y)
    retlist.append((left_x,top_y))
    
    return (code_string, retlist)

def block_type(image,pixtocheck,x,y):
    """check pixcount pix starting at x,y; return code from avg intensity"""
    intensity = 0
    for testx in range(x,x+pixtocheck):
        intensity += image.getpixel((testx,y))[0]
    intensity = intensity/pixtocheck
    if intensity > 192:
        retval = 0
    elif intensity > 64:
        retval = 1
    else:
        retval = 2
    return retval


def column_markers(page,min_runlength_inches=.2,zonelength_inches=.25):
    """given top line landmarks, find column x offsets by inspecting boxes

    The uppermost line forms the top of a box containing
    column headers.  This column header box is approximately 1/6" tall.
    
    We go halfway down into the column header box, looking for .24" 
    black rectangles which are spaced .14 inches from vertical lines 
    left and right; these represent the x offsets of vote opportunities.  

    The actual test is for runs of pixels of red intensity < 128.  
    The run must have only one miss for min_runlength_inches
    in a horizontal strip one pixel high.
    """
    columns = []
    image = page.image
    first_x = page.landmarks[0][0]
    top_y = (page.landmarks[0][1]+page.landmarks[1][1])/2
    top_y -= adj(0.01)

    twelfth = adj(0.083)
    min_runlength = adj(min_runlength_inches)
    true_pixel_width_of_votezone = adj(zonelength_inches)
    # go in 1" from edge, 
    # follow top line across, adjusting y as necessary, 
    black_run_misses = 0
    black_runlength = 0
    startx = first_x + 2
    endx = image.size[0] - const.dpi
    incrementx = 1
    page.ballot.log.debug("Looking for top line starting from (%d,%d)"%(startx,top_y))
    #print "Looking for top line starting from (%d,%d)"%(startx,top_y)
    # start by scanning downwards until you pick up the line
    counter = 0
    while True:
        pix = image.getpixel((startx,top_y))
        if pix[0]<128: break
        top_y += 1
        counter += 1
        if counter > (const.dpi/10):
            raise Ballot.BallotException, "couldn't find line atop columns"

    for x in range(startx,endx,incrementx):
        # if we lose the line,
        if image.getpixel((x,top_y))[0]>64:
            # go up or down looking for black pixel
            if image.getpixel((x,top_y-1))[0]<image.getpixel((x,top_y+1))[0]:
                top_y -= 1
            else:
                top_y += 1
        if image.getpixel((x,top_y+twelfth))[0] < 128:
            black_runlength += 1
            if black_runlength >= min_runlength:
                columns.append((x-black_runlength,top_y))
                black_runlength = 0
                black_run_misses = 0
        else:
            black_run_misses += 1
            if black_run_misses > 1:
                black_runlength = 0    
                black_run_misses = 0

    return columns
    # looking 1/12" down for quarter inches of black

def get_marker_offset(tm_markers,height):
    """how far has the timing mark at this height been offset from top_x"""
    xoffset = 0
    for tm_marker in tm_markers:
        if tm_marker[1]>height:
            xoffset = tm_marker[0] - tm_markers[0][0]
            break
    return xoffset

