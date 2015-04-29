# saguache_ballot.py implements the interface defined (well, suggested)
# in Ballot.py, in a Saguache/ESS-specific way.
# The Trachtenberg Election Verification System (TEVS)
# is copyright 2009, 2010 by Mitch Trachtenberg 
# and is licensed under the GNU General Public License version 2.
# (see LICENSE file for details.)

"""
Code for determining votes from 
ES&S ballots from Saguache County, Colorado
"""
import Image, ImageStat, ImageDraw, ImageFont
import Ballot
import const
import util
from ocr import ocr
from adjust import rotator


class SaguacheBallot(Ballot.Ballot):
    """Class representing ballots from Saguache CO (ESS).

    Each Saguache ballot has oval voting areas,
    and voting areas are grouped in boxed contests.
    Precinct coding is in a column just inboard from timing marks.

    The file name sagauche_ballot.py and the class name SaguacheBallot
    correspond to the brand entry in tevs.cfg, the configuration file.
    """

    def __init__(self, images, extensions):
        #convert all our constants to locally correct values
        # many of these conversions will go to Ballot.py,
        # extenders will need to handle any new const values here, however
        adj = lambda f: int(round(const.dpi * f))
        self.oval_size = (
            page.target_width,
            page.target_height
        )
        self.oval_margin = page.margin_width#XXX length should be in config or metadata
        self.min_contest_height = adj(const.minimum_contest_height_inches)
        self.vote_target_horiz_offset = adj(const.vote_target_horiz_offset_inches)
        self.writein_xoff = adj(2.5) #XXX
        self.writein_yoff = adj(.6)
        self.allowed_corner_black = adj(const.allowed_corner_black_inches)
        super(SaguacheBallot, self).__init__(images, extensions)

    def find_landmarks(self, page):
        """ retrieve landmarks for Saguache images, set tang, xref, yref

        Landmarks for the Saguache Ballot will be the 
        (x, y) pairs at the center of the two upper plus in a circle
        registration marks.

        They are searched for in the upper left and upper right
        square inches of the image.
        
        The coordinates of the pair at upper left are returned, along
        with a rotation value calculated from the two pairs.

        Ballots would be rejected at this stage if there is excessive
        black in any corner, potentially indicating a scanning problem.

        Current error handling will generally log and terminate 
        on first BallotException.
        """
        crop = page.image.crop((0,
                              0,
                              const.dpi,
                              const.dpi))
        (a, b) = find_plus_target(crop, const.dpi)
        crop = page.image.crop((page.image.size[0] - const.dpi,
                              0,
                              page.image.size[0],
                              const.dpi))
        (c, d) = find_plus_target(crop, const.dpi)
        if a == -1 or b == -1 or c == -1 or d == -1:
            raise Ballot.BallotException("Could not find landmarks")
        # adjust c to ballot coordinates from crop coordinates
        c += (page.image.size[0] - const.dpi)

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


        xoff = a
        yoff = b

        shortdiff = d - b
        longdiff = c - a
        rot = -shortdiff/float(longdiff)
        if abs(rot) > const.allowed_tangent:
            raise Ballot.BallotException(
                "Tilt %f of %s exceeds %f" % (rot, page.filename, const.allowed_tangent)
            )

        return rot, xoff, yoff 

    def get_layout_code(self, page):
        """ Determine the code from the column by the timing marks 

        ESS/Saguache ballots have coding information only on the front
        of the sheet.  The approach used here is to try looking for 
        coding information with timing marks on the left and, if that
        returns no timing_marks, to search for timing marks on the right.

        If no code is picked up (as will occur if it is a back),
        the code is taken from the front, with "BACK" prepended.

        To accomodate back-first ballots, we would need to add additional
        handling.  Will be implemented as extended flip in class DuplexBallot
        in Ballot.py
        """
        barcode, tm_list = timing_marks(page.image,
                                         page.xoff,
                                         page.yoff,
                                         (const.dpi/8),
                                         const.dpi)
        # If this is a back page, need different arguments
        # to timing marks call; so have failure on front test
        # trigger a back page test
        if len(tm_list) != 38:
            inch_from_end = page.xoff + page.image.size[0] - const.dpi
            barcode, tm_list = timing_marks(page.image,
                                             inch_from_end,
                                             page.yoff,
                                             -(const.dpi/8),
                                             const.dpi)


        page.tm_list = tm_list
        print "Barcode [%s]" % (barcode, )
        if len(barcode)<2:
            barcode = "BACK"+self.pages[0].barcode
        page.barcode = barcode
        return barcode

    def extract_VOP(self, page, rotatefunc, scale, choice):
        """Extract a single oval, or writein box, from the specified ballot.
        
        Note that cropstats is C code in Imaging-1.1.7, most of which 
        fine-tunes the location of a Hart ballot vote box. The fine-tuning
        is left OFF in this call to cropstats.

        The "suspicious" value returned from cropstats is toggled if
        there is any dark pixel in the central region of the oval; this
        may be more appropriate to rectangular vote ops as in Hart.

        The IStats class in Ballot provides more convenient access
        to the list of information returned from cropstats.

        The determination of whether a vote target was actually voted,
        or whether a vote target represents a write-in, is currently
        performed by the default functions set into the Ballot Extensions
        object.  These functions may be overriden. XXX Example!
        """
        adj = lambda f: int(round(const.dpi * f))
        iround = lambda x: int(round(x))
        x, y = choice.coords()
        x = int(x)
        y = int(y)
        margin_width = page.margin_width
        margin_height = page.margin_height

        #BEGIN SHARABLE
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
        #END SHARABLE
        ow = page.target_width
        oh = page.target_height

        stats = Ballot.IStats(page.image.cropstats(
            const.dpi,
            self.vote_target_horiz_offset, 
            x, y,
            ow, oh,
            0 # NOTE, this turns OFF fine adjustment, tuned to Hart in Imaging
        ))

        #can be in separate func?
        cropx = stats.adjusted.x
        cropy = stats.adjusted.y
        crop = page.image.crop((
            cropx - margin_width,
            cropy - margin_height,
            cropx + margin_width + ow, 
            cropy + margin_height + oh
        ))

        #can be in separate func?
        voted, ambiguous = self.extensions.IsVoted(crop, stats, choice)
        writein = False
        if voted:
           writein = self.extensions.IsWriteIn(crop, stats, choice)
        if writein:
            crop = page.image.crop((
                 cropx - margin_width,
                 cropy - margin_height,
                 min(cropx + self.writein_xoff + margin_width,
                     page.image.size[0]-1),
                 min(cropy + self.writein_yoff + margin_height,
                     page.image.size[1]-1)
            ))

        return cropx, cropy, stats, crop, voted, writein, ambiguous

    def build_layout(self, page):
        """ get layout and ocr information from Saguache ballot

        Building the layout will be the largest task for registering
        a new ballot brand which uses a different layout style.

        For ESS/Saguache, we are making the assumption that we are
        provided with PDF print files used for printing the ballots;
        this allows us to assume all template images will remain
        unmarked by voters, further allowing us to search for ovals
        by testing for a pattern.

        In ESS/Saguache, there is a boxed region at the top and bottom
        which contains black rectangles representing the vertical channels
        in which vote ovals will be found.  We get those markers,
        then search down those channels for ovals and text in build_regions,
        assuming that ovals will be dark areas meeting pattern conditions,
        and marks in the vote channels not matching ovals must be text 
        unrelated to a particular vote opportunity, which we then treat
        as contest headings.  

        As we walk through each column in build_regions, 
        we add new Contests to the contest
        list, and add Choices to the previously added Contest.

        """
        dpi = const.dpi
        dpi2, dpi4, dpi16 = dpi/2, dpi/4, dpi/16
        xend, yend = page.image.size[0], page.image.size[1]
        top_columns = column_markers(page.image,
                                     page.tm_list[0],
                                     const.dpi,
                                     .2,
                                     .25)
        page.top_columns = top_columns
        regionlist = self.build_regions(page,
                                   page.tm_list,
                                   const.dpi,
                                   stop=False)

        return regionlist

    def build_regions(self, page, tm_list, dpi, stop=True, verbose=False):
        """ Build regions returns a list of Contests found on the page"""
        regionlist = []
        onethird = int(round(dpi/3.))
        twelfth = int(round(dpi/12.))
        guard_twentieth = int(round(dpi/20.))
        guard_tenth = int(round(dpi/10.))
        guard_fifth = int(round(dpi/5.))
        cropnum = 0
        column_width = 0
        top_columns = page.top_columns
        tm_list = page.tm_list
        try:
            column_width = top_columns[1][0] - top_columns[0][0]
        except:
            column_width = 2*dpi
        for top_xy in top_columns:
            matched = []
            ovals = self.column_oval_search(page, top_xy[0])
            textzones = self.column_textzone_search(page, top_xy[0]+(column_width/2))
            ovals.sort()
            textzones.sort()
            zonestart = 0
            zoneend = 0
            for textzone in textzones:
                #print "Processing textzone at (%d, %d)" % (top_xy[0], textzone)
                match =  0
                # any text beginning from 1/16" above the oval 
                # to 1/6" below
                # is associated with the oval
                for oval in ovals:
                    if textzone > (oval - dpi/16) and textzone < (oval + dpi/4):
                        match = oval
                        #print "-->Match for oval %d" % (oval)
                if match>0:
                    if zonestart > 0 and zoneend > zonestart:
                        #output last nonmatching textzone
                        croplist = (top_xy[0] - dpi/8,
                                    zonestart,
                                    top_xy[0]+column_width - dpi/4,
                                    zoneend )
                        #print "Croplist to output", croplist
                        crop = page.image.crop(croplist)
                        
                        # The extensions object offers the ability
                        # to provide the ocr and text cleanup functions
                        # of your choice.
                        text = self.extensions.ocr_engine(crop)
                        text = self.extensions.ocr_cleaner(text)

                        zonestart = 0
                        zoneend = 0
                        print "Contest Text: %s" % (text, )
                        regionlist.append(
                            Ballot.Contest(top_xy[0],
                                           zonestart,
                                           column_width,
                                           dpi,
                                           0,
                                           text)
                            )
                    # get text for ovals only once
                    if match not in matched:
                        #print "-->(not previously matched.)"
                        croplist = (top_xy[0]+dpi/4, match - (dpi/50),
                                    top_xy[0]+column_width - dpi/4, match + (dpi/3))
                        #print croplist
                        crop = page.image.crop(croplist)
                        text = self.extensions.ocr_engine(crop)
                        text = self.extensions.ocr_cleaner(text)
                        print "Oval (%d, %d): %s" % (top_xy[0],
                                                    match,
                                                    text.strip())
                        if len(regionlist)>0:
                                regionlist[-1].append( 
                                    #TODO add x2, y2, remove text
                                    Ballot.Choice(top_xy[0], match, text)
                                    )
                        # now enter the just matched oval into a list
                        # of already printed ovals
                        matched.append(match)
                else:
                    if zonestart == 0:
                        zonestart = textzone 
                    # textzone includes both the 1/32 which may have contributed
                    # a dark pixel into the triggering crop, 
                    # and an additional 16th inch to take into account the chance
                    # there was another dark zone not quite long enough 
                    # to become a text zone
                    zoneend = textzone + (dpi/32) + (dpi/16)
                    #print "Textzone at y %d is not associated with an oval." % (textzone, )
        return regionlist

    def column_oval_search(self, page, top_x, dpi=300):
        """return list of probable oval y offsets"""
        # ovals will be 1/4" followed by minimum 1/6" horiz guard zone
        # and 1/10" tall followed by minimum 1/10" vertical guard zone
        print "Column oval search for column w/ top_x = ", top_x
        oval_width = self.oval_size[0]
        oval_height = self.oval_size[1]

        image = page.image
        changelist = []
        contig = 0
        print top_x
        skip = 0
        for y in range(page.dpi, image.size[1] - page.dpi, 1):
            # skip is set to 1/4" when oval found, 
            # because ovals will be separated at 1/3" minimum
            if skip > 0: 
                skip -= 1
                continue

            # set possible to True if you pass a set of initial tests
            possible = False

            # First filtering test:
            # search for any dark pixel in the oval zone
            # and at least some accompanying darkening of 1 pix tall stripe
            croplist1 = (top_x,
                        y,
                        top_x + oval_width,
                        y+1)
            crop1 = image.crop(croplist1)
            cropstat1 = ImageStat.Stat(crop1)
            if cropstat1.mean[0]<254 and cropstat1.extrema[0][0]<192:
                # Passed first test, conduct further checks.
                # an oval will have:
                #  no dark pixel centered approx 1/20" down
                #  another dark pixel centered approx 1/10" down
                #  and a dark pixel on either side approx 1/20" down
                for y2 in range(y+oval_height-2, y+oval_height+2):
                    croplist2 = (top_x,
                                 y2,
                                 top_x + oval_width,
                                 y2+1)
                    crop2 = image.crop(croplist2)
                    cropstat2 = ImageStat.Stat(crop2)
                    # croplist three represents the oval center
                    croplist3 = (top_x+(3*page.dpi/32), y+(oval_height/2), top_x+(5*page.dpi/32), y+(oval_height/2)+1)
                    crop3 = image.crop(croplist3)
                    cropstat3 = ImageStat.Stat(crop3)
                    croplist4 = (top_x-(page.dpi/16), y+(oval_height/2), top_x+(page.dpi/16), y+(oval_height/2)+1)
                    crop4 = image.crop(croplist4)
                    cropstat4 = ImageStat.Stat(crop4)
                    croplist5 = (top_x-((3*page.dpi)/16), y+(oval_height/2), top_x+((5*page.dpi)/16), y+(oval_height/2)+1)
                    crop5 = image.crop(croplist5)
                    cropstat5 = ImageStat.Stat(crop5)
                    # cropstat3 must not have dark pixels
                    # if it is the center of an empty oval
                    # cropstat4 and 5 must have dark pixels
                    # as they are the edges of an empty oval
                    if (cropstat2.mean[0]<254 
                        and cropstat2.extrema[0][0]<128 
                        and cropstat4.extrema[0][0]<128 
                        and cropstat5.extrema[0][0]<128 
                        and not (cropstat3.extrema[0][0]<128)):
                        possible = True
                        break
            # if you passed all initial tests, check for the guard zones
            if possible:

                # to right of oval from oval top for 18/100" down
                croplist1 = (top_x+(5*page.dpi/16), y, top_x+((6*page.dpi)/16), y+((18*page.dpi)/100))
                crop1 = image.crop(croplist1)
                cropstat1 = ImageStat.Stat(crop1)
                # beneath oval for 1/10" from oval start for 1/3" horiz
                croplist2 = (top_x, y+((12*page.dpi)/100),
                             top_x + (page.dpi/3), y+((18*page.dpi/100)))
                crop2 = image.crop(croplist2)
                cropstat2 = ImageStat.Stat(crop2)
                # if no dark pixel in guard zone, this is very likely an oval
                # so append this y offset to the list to be returned
                if cropstat1.extrema[0][0]>=128 and cropstat2.extrema[0][0]>=128:
                    # if you find an oval, you won't find another
                    # for at least 1/3"; let's skip forward 1/4"
                    skip = page.dpi/4
                    changelist.append(y)

        #print "Ovalstarts", changelist
        return changelist

    def column_textzone_search(self, page, top_x):
        print "Column textzone search for column w/ center x = ", top_x
        textzones = []
        contig = 0
        dpi = page.dpi
        image = page.image
        #skip = 0
        for y in range(dpi, image.size[1] - dpi, 1):
            #if skip>0:
            #    skip -= 1
            #    continue
            croplist = (top_x-(dpi/2),
                        y,
                        top_x + (dpi/2),
                        y+1)
            crop = image.crop(croplist)
            cropstat = ImageStat.Stat(crop)
            if cropstat.extrema[0][0] < 192:
                if contig > (dpi/32):
                    #print "Textzone starts at %d" % (y-contig)
                    #skip = (dpi/12)
                    textzones.append(y-contig)
                    contig = 0
                else:
                    contig += 1
            else:
                contig = 0
        #print "Textzones start", textzones
        return textzones



def find_plus_target(image, dpi=300,
                     full_span_inches=0.18,
                     line_width_inches=0.01,
                     circle_radius_inches=0.03):
    """return ulc of the center of first "+" target in the image, or -1, -1"""
    full_span_pixels = int(round(full_span_inches * dpi))
    line_width_pixels = int(round(line_width_inches * dpi))
    circle_radius_pixels = int(round(circle_radius_inches * dpi))
    return_x = -1
    return_y = -1
    min_hrun = 50
    y_darknesses = []
    x_darknesses = []
    # for candidates, look for a white black white transition
    # when found, check for line below at half span width +/- 2 pixels
    # if found, look for a white black white transition at
    # at full span width less 2 pixels
    # If pass, all situation is likely; optionally check further;
    # possibly for white black white seq of one or more quadrants
    for y in range(0, image.size[1]-full_span_pixels):
        for x in range(circle_radius_pixels, image.size[0]-circle_radius_pixels):
            if (image.getpixel((x, y))[0] < 128 
                and image.getpixel((x-1, y))[0]>=128 
                and image.getpixel((x+(2*line_width_pixels), y))[0]>=128):
                if ((image.getpixel((x, y+full_span_pixels-2))[0]<128
                    or image.getpixel((x+1, y+full_span_pixels-2))[0]<128
                    or image.getpixel((x-1, y+full_span_pixels-2))[0]<128)
                    and (image.getpixel((x+(2*line_width_pixels),
                                         y+full_span_pixels - 2))[0]>=128)):
                    try:
                        hline = image.crop((x-circle_radius_pixels,
                                            y+(full_span_pixels/2)-2,
                                            x+circle_radius_pixels,
                                            y+(full_span_pixels/2)+2))
                        hlinestat = ImageStat.Stat(hline)
                        if hlinestat.mean[0]>64 and hlinestat.mean[0]<192:
                            # we need to see some extremely white pixels nearby
                            white1 = image.crop((x+line_width_pixels+1,
                                                y+ (full_span_pixels/10),
                                                x + (2*line_width_pixels),
                                                y + (full_span_pixels/5)))
                            whitestat1 = ImageStat.Stat(white1)
                            white2 = image.crop((x-(2*line_width_pixels),
                                                y+ (full_span_pixels/10),
                                                x - 1,
                                                y + (full_span_pixels/5)))
                            whitestat2 = ImageStat.Stat(white2)
                            if whitestat1.mean[0]>224 and whitestat2.mean[0]>224:
                                return (x, y+(full_span_pixels/2))
                    except:
                        pass
    return (-1, -1)
                    
def timing_marks(image, x, y, backup, dpi):
    """locate timing marks and code, starting from ulc + symbol"""
    # go out from + towards left edge by 1/8", whichever is closer
    # down from + target to first dark, then left to first white
    # and right to last white, allowing a pixel of "tilt"
    retlist = []
    half = int(round(dpi/2.))
    third = int(round(dpi/3.))
    down = int(round(dpi/3.))
    sixth = int(round(dpi/6.))
    twelfth = int(round(dpi/12.))
    search_x = x - backup
    initial_y = y + down + twelfth
    
    # search up and down to see extent of black, 
    # do horizontal search from vertical center
    blacks_above = 0
    blacks_below = 0
    for search_inc in range(sixth):
        if image.getpixel((search_x, initial_y + search_inc))[0]<128:
            blacks_below += 1
        if image.getpixel((search_x, initial_y - search_inc))[0]<128:
            blacks_above += 1
    final_y = initial_y + ((blacks_below-blacks_above)/2)
    top_y = initial_y - blacks_above

    blacks_behind = 0
    misses = 0
    for search_inc in range(dpi):
        if search_x > search_inc:
            if image.getpixel((search_x-search_inc, final_y))[0]<128:
                blacks_behind += 1
                misses = 0
            else:
                misses += 1
            if misses > 1:
                break
    blacks_ahead = 0
    misses = 0
    for search_inc in range(dpi):
        if search_x > search_inc:
            if image.getpixel((search_x+search_inc, final_y))[0]<128:
                blacks_ahead += 1
                misses = 0
            else:
                misses += 1
            if misses > 1:
                break
    #print "At y =", final_y, "width is", blacks_behind+blacks_ahead
    left_x = search_x - blacks_behind
    #print "ULC = (", search_x - blacks_behind, top_y, ")"
    retlist.append( (search_x - blacks_behind, top_y) )
    # now go down 1/2" and find next ulc, checking for drift
    top_y += half
    code_string = ""
    zero_block_count = 0
    while True:
        (left_x, top_y) = adjust_ulc(image, left_x, top_y)
        if left_x == -1: break
        # check for large or small block to side of timing mark
        if backup > 0:
            # dealing with a left side, proper orientation; get block 
            block = block_type(image, dpi/4, left_x+half, top_y+twelfth)
        else:
            block=0
        if block==0: 
            zero_block_count += 1
        elif block==1:
            code_string = "%s%dA" % (code_string, zero_block_count)
            zero_block_count = 0
        elif block==2:
            code_string = "%s%dB" % (code_string, zero_block_count)
            zero_block_count = 0
            
        retlist.append((left_x, top_y))
        # now go down repeated 1/3" and find next ulc's until miss
        top_y += third
    # try finding the last at 1/2" top to top
    left_x = retlist[-1][0]
    top_y = retlist[-1][1]
    top_y += half
    (left_x, top_y) = adjust_ulc(image, left_x, top_y)
    retlist.append((left_x, top_y))
    
    return (code_string, retlist)
    # get length of first block; 3/4" signals left, 1/4" signals right
    
    # repeat search 1/2" below, then at 1/3" intervals
    # when a 1/3" interval fails, try a 1/2" interval to get the last

    # at v-center of each timing mark, search out horizontally for length
    # for existence and length of additional block

def block_type(image, pixtocheck, x, y):
    """check line for quarter inch and return pct below 128 intensity"""
    intensity = 0
    for testx in range(x, x+pixtocheck):
        intensity += image.getpixel((testx, y))[0]
    intensity = intensity/pixtocheck
    if intensity > 192:
        retval = 0
    elif intensity > 64:
        retval = 1
    else:
        retval = 2
    return retval


def adjust_ulc(image, left_x, top_y):
    target_intensity = 255
    max_adjust = 5
    while max_adjust > 0 and target_intensity > 128:
        max_adjust -= 1
        left_target_intensity = image.getpixel((left_x-2, top_y))[0]
        target_intensity = image.getpixel((left_x, top_y))[0]
        right_target_intensity = image.getpixel((left_x+2, top_y))[0]
        above_target_intensity = image.getpixel((left_x, top_y-2))[0]
        above_right_target_intensity = image.getpixel((left_x+2, top_y-2))[0]
        above_left_target_intensity = image.getpixel((left_x-2, top_y-2))[0]
        below_target_intensity = image.getpixel((left_x, top_y+2))[0]
        below_left_target_intensity = image.getpixel((left_x-2, top_y+2))[0]
        below_right_target_intensity = image.getpixel((left_x+2, top_y+2))[0]
        #print above_left_target_intensity, above_target_intensity, above_right_target_intensity
        #print left_target_intensity, target_intensity, right_target_intensity
        #print below_left_target_intensity, below_target_intensity, below_right_target_intensity
        if below_target_intensity > 64 and target_intensity > 64:
            left_x += 2
        elif below_left_target_intensity <= 127:
            left_x -= 2
        if right_target_intensity > 64 and target_intensity > 64:
            top_y += 2
        elif above_right_target_intensity <= 127:
            top_y -= 2
    if max_adjust == 0: 
        return(-1, -1)
    return (left_x, top_y)

def column_markers(image, tm_marker, dpi, min_runlength_inches=.2, zonelength_inches=.25):
    """given timing marks, find column x offsets"""
    columns = []
    top_y = tm_marker[1]
    first_x = tm_marker[0]
    twelfth = int(round(dpi/12.))
    min_runlength = int(round(dpi * min_runlength_inches))
    true_pixel_width_of_votezone = int(round(dpi*zonelength_inches))
    # go in 1" from edge, 
    # follow top line across, adjusting y as necessary, 
    black_run_misses = 0
    black_runlength = 0
    if first_x > (image.size[0]/2):
        run_backwards = True
        startx = first_x - dpi
        endx = dpi/2
        incrementx = -1
    else:
        run_backwards = False
        startx = first_x+dpi
        endx = image.size[0]-dpi
        incrementx = 1
        
    for x in range(startx, endx, incrementx):
        # if we lose the line,
        if image.getpixel((x, top_y))[0]>64:
            # go up or down looking for black pixel
            if image.getpixel((x, top_y-1))[0]<image.getpixel((x, top_y+1))[0]:
                top_y -= 1
            else:
                top_y += 1
        if image.getpixel((x, top_y+twelfth))[0] < 128:
            black_runlength += 1
            if black_runlength >= min_runlength:
                if run_backwards:
                    # instead of subtracting min_runlength
                    # subtract true_pixel_width_of_votezone
                    # to establish actual minimum x of votezone
                    columns.append((x+min_runlength-true_pixel_width_of_votezone, top_y))
                else:
                    columns.append((x-black_runlength, top_y))
                black_runlength = 0
                black_run_misses = 0
        else:
            black_run_misses += 1
            if black_run_misses > 1:
                black_runlength = 0    
                black_run_misses = 0

    if run_backwards:
        columns.reverse()
    return columns
    # looking 1/12" down for quarter inches of black


