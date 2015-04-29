# sequoia_ballot.py implements the interface 
# in Ballot.py, and is an example of extending TEVS to new ballot types.
# It is not yet a complete sequoia implementation!
# The Trachtenberg Election Verification System (TEVS)
# is copyright 2009, 2010 by Mitch Trachtenberg 
# and is licensed under the GNU General Public License version 2.
# (see LICENSE file for details.)

import Ballot
import const
from adjust import rotator
import Image,ImageStat
from demo_utils import *
import ocr
from cropstats import cropstats
block_zone_upper_y = 0.5
block_zone_width_to_crop = 0.7
block_zone_width = 0.57
block_zone_height = 1.5
minimum_repeats = 0.05
v_offset_to_dash_center = 0.03
v_delta_dash_to_dash = 0.17
column1_offset = 2.95
column2_offset = 5.95
right_block_offset = 6.1

# the function below overrides any IsWriteIn extension
def IsWriteIn(im,stats,choice):
    """ All we have to go on is a text-free box."""
    return len(choice.description)<3

def find_y_of_landmark_pattern(crop,dpi,offset1,offset2):
    """ return first y offset at which pattern condition is met, or -1 """
    adj = lambda f: int(round(const.dpi * f))
    vertical_dist_top_dashes = adj(v_delta_dash_to_dash)
    vertical_dist_to_next_center = adj(v_delta_dash_to_dash * 1.25)
    minimum_repeats = adj(0.02)
    contig = 0
    retval = -1
    for n in range(dpi/2):
        match = False
        pix1 = crop.getpixel((offset1,n))
        pix2 = crop.getpixel((offset2,n))
        pix3 = crop.getpixel((offset1,n+((2*vertical_dist_top_dashes)/3)))
        pix4 = crop.getpixel((offset2,n+((2*vertical_dist_top_dashes)/3)))
        pix5 = crop.getpixel((offset1,n+vertical_dist_to_next_center))
        pix6 = crop.getpixel((offset2,n+vertical_dist_to_next_center))
        # need black/white/black with white at both points in center
        if (pix1[0]<128 or pix2[0]<128)  and (pix3[0]>128 and pix4[0]>128) and (pix5[0]<128 or pix6[0]<128):
            contig = contig + 1
        else:
            contig = 0
        if contig > minimum_repeats:
            retval = n - minimum_repeats
            break

    return retval
        

def get_offsets_and_tangent_from_blocks(im,dpi,dash_sep_in_pixels):
    """ locate marks at top left, right of image
    
    return the x,y coordinates of the large timing marks
    at upper left and upper right, 
    as well as the tangent of the tilt angle between them.
    """
    found_left = False
    found_right = False
    iround = lambda x: int(round(x))
    adj = lambda f: int(round(const.dpi * f))
    croptop = adj(block_zone_upper_y )
    cropbottom = croptop + dpi
    leftstart = 0
    leftend = adj(block_zone_width_to_crop)
    rightstart = im.size[0] - adj(block_zone_width_to_crop)
    rightend = im.size[0] - 1
    vertical_dist_top_dashes = dash_sep_in_pixels
    vertical_dist_block_dashes = iround(dpi * .17)

    leftcrop = im.crop((leftstart,croptop,leftend,cropbottom))
    rightcrop = im.crop((rightstart,croptop,rightend,cropbottom))

    # look for black white black bar pattern and return y of pattern start
    scanx = adj(0.1)
    leftstarty = find_y_of_landmark_pattern(leftcrop,dpi,scanx,scanx*2)
    if leftstarty == -1:
        raise Ballot.BallotException("Failed to find left landmark.")

    rightstarty = find_y_of_landmark_pattern(rightcrop,dpi,scanx,scanx*2)
    if rightstarty == -1:
        raise Ballot.BallotException("Failed to find right landmark.")

    leftdashcentery = leftstarty + adj(v_offset_to_dash_center)
    rightdashcentery = rightstarty + adj(v_offset_to_dash_center)


    # now go leftward from scanx
    # along the center of the top dash until white or off edge
    leftstartx = 0
    scanx = adj(0.2)
    for n in range(scanx):
        pix = leftcrop.getpixel(((scanx - n),
                                 leftdashcentery))
        if pix[0]>128:
            leftstartx = scanx - n
            break

    rightstartx = 0
    for n in range(scanx):
        pix = rightcrop.getpixel(((scanx - n),
                                 rightdashcentery))
        if pix[0]>128:
            rightstartx = scanx - n
            break

    return( leftstartx,
            leftstarty+croptop,
            rightstart + rightstartx,
            rightstarty+croptop,
            (rightstarty-leftstarty)/(im.size[0]-adj(block_zone_width_to_crop)))        

def get_code_from_blocks(im,dpi,leftstartx,leftstarty,rightstartx,rightstarty):
    """read dash pattern encoding layout and return encoded int
    
    There are dash blocks at upper left and right.  The right represents
    the eight least significant digits and the left the 8 more significant
    digits.  Each bit is represented by the presence (1)
    or absence (0) of a center dash between the two surround dashes, with
    less significant digits lower in the pattern.

    The encoding is also printed to the left of the right dash block.
    """
    iround = lambda x: int(round(x))
    adj = lambda f: int(round(const.dpi * f))
    leftstartx = iround(leftstartx)
    leftstarty = iround(leftstarty)
    rightstarty = iround(rightstarty)
    leftcrop = im.crop(
        (max(0,leftstartx),
         leftstarty,
         leftstartx+adj(block_zone_width_to_crop),
         leftstarty+adj(block_zone_height)
         )
        )

    rightcrop = im.crop(
        (leftstartx + adj(right_block_offset),
         rightstarty,
         im.size[0]-1,
         rightstarty+adj(block_zone_height)
         )
        )

    leftdashcentery = adj(v_offset_to_dash_center)
    rightdashcentery = adj(v_offset_to_dash_center)


    scanx = adj(block_zone_width_to_crop/2.)
    # to capture code, check the eight possible code zones of each crop
    # starting with left, continuing to right
    accum = 0
    for n in range(1,9):
        accum = accum * 2
        testspot = ((adj(0.3),
                     adj(.045) + adj(n * v_delta_dash_to_dash)))

        pix = leftcrop.getpixel(testspot)
        if pix[0]<128:
            accum = accum + 1

    for n in range(1,9):
        accum = accum * 2
        testspot = ((adj(0.3),
                    adj(.045) + adj(n * v_delta_dash_to_dash)))
        pix = rightcrop.getpixel(testspot)
        if pix[0]<128:
            accum = accum + 1

    return ("%d" % (accum,))

def build_template(im,dpi,code,xoff,yoff,tilt,front=True):
    """build template of arrow locations

    When a ballot image is used for template construction, 
    it is assumed that code will have derotated it first!

    This code is not yet general; it assumes two arrow columns
    at set locations.  It locates arrows within those locations
    by searching for at least 0.05" of vertical contiguous black
    in locations which would correspond to the arrow head and
    the arrow tail, skipping at least the first vertical 1.5" on the front
    and the bottom 1.2" on both sides.

    The search for arrows begins only beneath a 0.6" long solid
    black bar (first channel <= 128 in range 0..255) at least 0.05" tall.
    """
    # find the locations of the arrow columns 
    # relative to xoff, yoff, and taking tilt into account
    #location_list = [(dpi,xoff,yoff,tilt)]
    # first set will be at just under 3" to right of xoff
    # next set will be at 6" to right of xoff.  
    # Both sets will be at least 0.08" tall after 0.1 inches.
    iround = lambda x: int(round(x))
    adj = lambda f: int(round(const.dpi * f))
    regionlist = []
    n = 0
    for x in (xoff+adj(column1_offset),xoff+adj(column2_offset)):
        # skip the code block if you're on a front
        if n==0 and front:
            starty = int(yoff + int(1.5*dpi))
        else:
            starty = int(yoff - 1)
        adjx,adjy = x,starty # XXX assuming ballot derotated by here
        # turn search on only when 0.06" of thick black line encountered
        contig = 0
        for y in range(adjy,im.size[1]):
            all_black_line = True
            for x2 in range(int(adjx+adj(0.1)),int(adjx+adj(0.5))):
                pix = im.getpixel((x2,y))
                if pix[0]>128:
                    all_black_line = False
                    break
            if all_black_line:
                contig = contig + 1
            else:
                contig = 0
            if contig > adj(0.05):
                if n==0:starty = y
                break
        if n==0:starty = starty + adj(0.2)
        # starty is now 0.2 inches below the first 0.6" dash of first column; 
        # arrows may be encountered from here until the column's height less
        # less 1.1 inches
        contig = 0
        # search at .15 inches in for first half of arrow
        searchx1 = x + adj(0.15)
        # search at .55 inches in for second half of arrow
        searchx2 = x + adj(0.55)
        skip = 0
        contest_x = 0
        contest_y = 0
        # stop looking for arrows at 1.2 inches up from the bottom 
        for y in range(int(starty),int(im.size[1]-adj(1.2))):
            if skip > 0:
                skip = skip - 1
                continue
            pix1 = im.getpixel((searchx1,y))
            pix2 = im.getpixel((searchx2,y))
            # look for .05 vertical inches of dark
            # in vertical strips that contain left
            # and right halves of arrow
            if pix1[0]<128 and pix2[0]<128:
                contig = contig + 1
                if contig > adj(0.05):
                    # this is an arrow
                    ll_x,ll_y = ((x,y))

                    if ll_x > (im.size[0] - 5):
                        ll_x = (im.size[0] - 5)
                    if ll_y > (im.size[1] - adj(0.5)):
                        ll_y = (im.size[1] - adj(0.5))
                    if ll_x < adj(2.5):
                        ll_x = adj(2.5)
                    if ll_y < adj(0.5):
                        ll_y = adj(0.5)
                    text,contest_text,contest_loc = get_text_for_arrow_at(im,ll_x,ll_y-contig-(0.04*dpi),const.dpi)
                    # new contest location? append contest, store contest size
                    if ((contest_x != contest_loc[0]) 
                        and contest_y != contest_loc[1]):
                        regionlist.append(Ballot.Contest(contest_x,contest_y,199,adj(5),0,contest_text))
                        contest_x = contest_loc[0]
                        contest_y = contest_loc[1]
                    else:
                        # update the bottom of the contest's bounding box
                        regionlist[-1].h = ll_y + adj(0.2)
                    #add x2, y2
                    regionlist[-1].append(Ballot.Choice(ll_x, ll_y, text))
                    

                    # skip past arrow
                    #y = y + (0.2 * dpi)
                    skip = adj(0.2)
                    # reset contig
                    contig = 0
    return regionlist

def get_text_for_arrow_at(im,x,y,global_dpi):
    """use tesseract to retrieve text corresponding to left of arrow

    Text associated with different arrows is separated by horizontal
    lines.  Find the y offsets of those lines and pass text between
    those offsets to tesseract, sending it a rectangle 2.25" wide from
    to the left of the arrow.

    The contest text is above a batch of arrows, and is separated from
    choice text by a thicker line.

    Text is run through ocr.clean_ocr_text and commas are deleted.

    Returns choice text, contest text, and crop rectangle for contest text.
    """
    # find center of arrow
    iround = lambda x: int(round(x))
    adj = lambda f: int(round(const.dpi * f))
    fortieth = int(global_dpi/40.)
    topline = int(y - fortieth)
    bottomline = int(y + int(global_dpi * .22))
    startx = int(x - global_dpi)
    starty = int(y + int(global_dpi * .07))
    for up in range(global_dpi/4):
        solid_line = True
        for xadj in range(global_dpi/4):
            pix = im.getpixel((startx+xadj,starty-up))
            if pix[0]>128:
                solid_line = False
                break
        if solid_line:
            topline = starty-up+1
            break

    for down in range(global_dpi/3):
        solid_line = True
        for xadj in range(global_dpi/4):
            pix = im.getpixel((startx+xadj,starty+down))
            if pix[0]>128:
                solid_line = False
                break
        if solid_line:
            bottomline = starty+down-1
            break
    # add one to accomodate rough top line
    topline += 1
    # need to back up to beginning of column, now using 2.25 inches
    crop_x = x - (global_dpi*2.25)
    crop_x = iround(crop_x)
    if crop_x<0:crop_x = 0

    if topline < 0: topline = 0
    if bottomline <= topline: bottomline = topline + 1
    if bottomline >= im.size[1]: bottomline = im.size[1]-1
    
    if crop_x < 0: crop_x = 0
    if x <= crop_x: x = crop_x + 1
    if x >= im.size[0]: x = im.size[0] - 1
    crop = im.crop((int(crop_x),
                    int(topline),
                    int(x),
                    int(bottomline)))
    text = ocr.tesseract(crop) # XXX self.extensions once in class
    text = ocr.clean_ocr_text(text)# XXX self.extensions once in class
    choice_topline = int(topline)
    # now repeat process but going up until thicker black; 
    # that will be the top of the contest
    contig = 0
    for up in range(global_dpi*3):
        solid_line = True
        for xadj in range(global_dpi/4):
            pix = im.getpixel((startx+xadj,topline-up))
            if pix[0]>128:
                solid_line = False
                contig = 0
                break
        if solid_line:
            contig = contig + 1
            if contig >= int(global_dpi/60.):
                topline = topline-up+1
                break
    contest_croplist = (int(crop_x),
                        int(topline),
                        int(x),
                        int(choice_topline ) 
                        )
    crop = im.crop(contest_croplist)
    contest_text = ocr.tesseract(crop)# XXX self.extensions once in class
    contest_text = ocr.clean_ocr_text(contest_text)# XXX self.extensions once in class
    text = text.replace("\n"," ").strip()
    contest_text = contest_text.replace("\n"," ").replace(",","").strip()

    return text, contest_text, contest_croplist



class SequoiaBallot(Ballot.Ballot):
    """Class representing a subset of Sequoia ballots.

    The file name sequoia_ballot.py and the class name SequoiaBallot
    correspond to the brand entry in tevs.cfg, 
    the configuration file.
    """

    def __init__(self, images, extensions):
        #convert all our constants to locally correct values
        # many of these conversions will go to Ballot.py,
        # extenders will need to handle any new const values here, however
        adj = lambda f: int(round(const.dpi * f))
        self.min_contest_height = adj(const.minimum_contest_height_inches)

        self.hotspot_x_offset_inches = adj(const.hotspot_x_offset_inches)
        self.vote_target_horiz_offset = adj(const.vote_target_horiz_offset_inches)
        self.writein_xoff = adj(-2.9) #XXX
        self.writein_yoff = adj(-0.2)
        self.allowed_corner_black = adj(const.allowed_corner_black_inches)
        super(SequoiaBallot, self).__init__(images, extensions)

    # Extenders do not need to supply even a stub flip
    # because flip in Ballot.py will print a stub message in the absence
    # of a subclass implementation
    #def flip(self, im):
    #    # not implemented for Demo
    #    print "Flip not implemented for Demo."
    #    return im

    def find_landmarks(self, page):
        """ retrieve landmarks for a sequoia ballot, set tang, xref, yref

        Landmarks for the sequoia ballot are the "dash blocks" at the
        upper left and upper right. These are retrieved by calling
        get_offsets_and_tangent_from_blocks.

        """
        iround = lambda x: int(round(x))
        adj = lambda f: int(round(const.dpi * f))
        dash_sep_in_pixels = adj(0.17)
        (a,b,c,d,tilt) = get_offsets_and_tangent_from_blocks(
            page.image,
            const.dpi,
            dash_sep_in_pixels)

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
            cropped = page.image.crop(area)
            area_stat = ImageStat.Stat(cropped)
            if area_stat.mean[0] < 16:
                raise Ballot.BallotException(errmsg % (corner, page.filename))

        xoff = a
        yoff = b

        shortdiff = d - b
        longdiff = c - a
        rot = -shortdiff/float(longdiff)
        if abs(rot) > const.allowed_tangent:
            raise Ballot.BallotException(
                "Tilt %f of %s exceeds %f" % (rot, page.filename, const.allowed_tangent)
            )
        self.log.debug("find landmarks returning %f,%d,%d, %d" %(rot,xoff,yoff,longdiff))
        # Ballot.py defines a distance y2y to be used for scaling between
        # template and ballot images.  Because both our landmarks are at the
        # top, we will consistently use longdiff for scaling in sequoia.
        return rot, xoff, yoff, longdiff 

    def get_layout_code(self, page):
        """ Determine the layout code by calling get_code_from_blocks.

        """
        iround = lambda x: int(round(x))
        adj = lambda f: int(round(const.dpi * f))
        barcode = get_code_from_blocks(page.image,
                                       const.dpi,
                                       page.xoff,
                                       page.yoff,
                                       page.image.size[0] 
                                       + page.xoff - adj(0.65),
                                       page.yoff  
                                       + (-page.rot * page.image.size[0]))    
        # If this is a back page, need different arguments
        # to timing marks call; so have failure on front test
        # trigger a back page test
        if barcode == -1:
            barcode = "BACK" + self.pages[0].barcode
        page.barcode = barcode
        return barcode

    def extract_VOP(self, page, rotatefunc, scale, choice):
        """Extract statistics for a single oval or writein from the ballot.

        """
        iround = lambda x: int(round(x))
        adj = lambda f: int(round(const.dpi * f))
        x, y = choice.coords()
        x = int(x)
        y = int(y)

        # NO horizontal margins in crop - grabbing region between marks!
        # const.margin_width_inches not used
        # hotspot_x_offset_inches IS used
        scaled_page_offset_x = page.xoff/scale
        scaled_page_offset_y = page.yoff/scale
        self.log.debug("Incoming coords (%d,%d), \
page offsets (%d,%d) template offsets (%d,%d)" % (
                x,y,
                page.xoff,page.yoff,
                scaled_page_offset_x,scaled_page_offset_y))
        # adjust x and y for the shift of landmark between template and ballot
        x = iround(x + scaled_page_offset_x - page.template.xoff)
        y = iround(y + scaled_page_offset_y - page.template.yoff)
        self.log.debug("Result of transform: (%d,%d)" % (x,y))
        
        x, y = rotatefunc(x, y, scale)
        cropx = x
        cropy = y
        cropy -= adj(.1)


        # NO horizontal margins in crop - grabbing region between marks!
        croplist = (
            cropx + self.hotspot_x_offset_inches ,
            cropy - page.margin_height,
            min(cropx + self.hotspot_x_offset_inches + page.target_width,
                page.image.size[0]-1), 
            min(cropy + page.margin_height + page.target_height,
                page.image.size[1]-1)
        )
        crop = page.image.crop(croplist)
        cropstat = ImageStat.Stat(crop)
        stats = Ballot.IStats(cropstats(crop,cropx,cropy))
        #can be in separate func?
        
        voted, ambiguous = self.extensions.IsVoted(crop, stats, choice)
        writein = False
        if voted:
           # extension is overriden with local function for this ballot type   
           writein = IsWriteIn(crop, stats, choice)
           if writein:
               x1 = min(self.writein_xoff+cropx,cropx)
               x2 = max(self.writein_xoff+cropx,cropx)
               y1 = min(self.writein_yoff+cropy,cropy + adj(.2))
               y2 = max(self.writein_yoff+cropy,cropy + adj(.2))
               crop = page.image.crop((
                       x1,
                       y1 - page.margin_height,
                       min(x2,page.image.size[0]-1),
                       min(y2 + page.margin_height,page.image.size[1]-1)
                       ))
        return cropx, cropy, stats, crop, voted, writein, ambiguous

    def build_layout(self, page):
        """ get layout and ocr information by calling build_template

        """
        adj = lambda f: int(round(const.dpi * f))
        regionlist = build_template(page.image,
                                    const.dpi,
                                    page.barcode,
                                    page.xoff,
                                    page.yoff,
                                    page.rot)
        return regionlist

