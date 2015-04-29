import sys
import pdb
import const
import Image
import ImageStat

"""
find_hline just checks for a dark region 1/3" long.
this can be tricked by individual characters.
scan_strips_for_horiz_line_y is slower, but checks for two connected
dark regions.

The numbers need to be adjusted for realistic line widths,
and we need to make sure we handle allowed tilts by not using
test regions so wide that a tilt will prevent the necessary
sharp intensity change.

Right now, scan_strips_for_horiz_line_y allows for 1/60" rise over a 2/3" span,
a tangent of .025 or a tilt of .025 radians, 1.4 degrees.

Sped up by starting closer to corners rather than at center.

Sped up by initial one pixel wide test for first dark pixel, 
then beginning line test at discovered dark pixel.

Speed up by using lines_connect only if the y offsets are not within 1 pix,
instead using stat test for darkness for the low tilt case.

"""
class LineUtilException(Exception):
    "Raised if analysis of a line cannot continue"
    pass

def follow_hline_to_corner(image,dpi,startx,hline,left=True):
    """Follow a dark line in a direction until it's not dark.

    Follow the line in image at y hline in one direction, tracking it
    as it rises or falls, until you encounter a 5 pixel gap.
    """
    retval = (0,0)
    if left:
        endx = dpi/30
        incr = -1
    else:
        endx = image.size[0] - dpi/30
        incr = 1

    lastred = 0
    possible = False
    for x in range(startx,endx,incr):
        # test for end of line by confirming 
        # no dark red pixels in next 3 moves
        if possible:
            croplist = (min(x,x+3*incr),hline-3,max(x,x+3*incr),hline+3)
            crop = image.crop(croplist)
            stat = ImageStat.Stat(crop)
            thisred = stat.extrema[0][0]
            if thisred >= const.line_exit_threshold:
                retval = (x,hline)
                break
        else:
            possible = False
        croplist = (x,hline - 3,x+1,hline+3)
        crop = image.crop(croplist)
        stat = ImageStat.Stat(crop)
        thisred = stat.extrema[0][0]
        data = crop.getdata()
        # if the top is darker than the bottom, move up a pixel,
        # or vice versa
        line_top_brightness = data[0][0]+data[1][0]+data[2][0] 
        line_bottom_brightness = data[3][0]+data[4][0]+data[5][0]
        if line_top_brightness > (line_bottom_brightness+5):
            hline += 1
        elif (line_top_brightness+5) < line_bottom_brightness: 
            hline -= 1
        # if you find a big change in intensity
        # and the darkest red in your crop is above a threshold,
        # you may have reached the end; test next time
        #if abs(lastred - thisred)>32 and thisred > const.line_exit_threshold:
        if thisred > const.line_exit_threshold:
            #print "Possible line end at",x
            #pdb.set_trace()
            possible = True
        lastred = thisred
    return retval

def find_hline(image,dpi,starting_x_offset,starting_y_offset=150,top=True):
    """ Scan inboard for a sharp drop in avg intensity of center 1/3 inch.

    Line detection is a search for a sharp drop in the average intensity
    of the center 1/3", between offset pixels inboard and one inch inboard.
    The result of the sharp intensity drop must be below half intensity.
    """
    retval = starting_y_offset
    lastred = 255
    one_sixth = dpi/6
    if top:
        starty = starting_y_offset
        endy = dpi
        incr = 1
    else:
        starty = image.size[1] - starting_y_offset
        endy = image.size[1] - dpi
        incr = -1
    for y in range(starty,endy,incr):
        croplist = ((image.size[0]/2) - one_sixth,
                    y,
                    (image.size[0]/2) + one_sixth,
                    y + 1)
        crop = image.crop(croplist)
        stat = ImageStat.Stat(crop)
        thisred = int(stat.mean[0])
        # a line must be below a threshold and should
        # be substantially darker than the area just before; how substantial
        # will be a tuned value, trying 32 for starters
        if abs(thisred-lastred)>32 and thisred <= const.line_darkness_threshold:
            retval = y
            break
        lastred = thisred
        
    return retval

def lines_connect(image,a,b,allowed_misses=1):
    """ Determine if there is a continuous stretch of dark pixels from a to b"""
    x1 = a[0]
    y1 = a[1]
    x2 = b[0]
    y2 = b[1]
    h_dist = x2 - x1

    # if y1 and y2 are within 1, crop y level line and use ImageStat
    """if abs(y1-y2) <= 1:
        miny = min(y1,y2)
        crop = image.crop((x1,miny,x2,miny+1))
        stat = ImageStat.Stat(crop)
        if stat.mean[0] < 128:
            return True
        else:
            return False
    """    
    
    # walk from x1 to x2, interpolating y between y1 and y2, 
    # failing if cannot confirm all pixels have dark pixels 
    # within one above or below
    walked = 0
    problem_count = 0
    for x in range(x1,x2,1):
        y = int(round(((y1*(h_dist-walked))+(y2*walked))/float(h_dist)))
        walked += 1
        p = image.getpixel((x,y))
        p_above = image.getpixel((x,y-1))
        p_below = image.getpixel((x,y+1))
        if ((p[0] >= const.line_exit_threshold)
            and (p_above[0] >= const.line_exit_threshold)
            and (p_below[0] >= const.line_exit_threshold)): 
            problem_count += 1
            if problem_count > allowed_misses: 
                break
    return (problem_count <= allowed_misses)

def scan_strips_for_horiz_line_y(image,dpi,starting_x_offset, starting_y_offset=150,height_to_scan=300,top=True):
    """ Scan inboard for a sharp drop in avg intensity of center 1/3 inch.

    Line detection is a search for a sharp drop in the average intensity
    of two near-center 1/6" regions, within 1/60" of one another vertically,
    between starting_y_offset pixels inboard and one inch inboard.
    The result of the sharp intensity drop must be below half intensity.
    """
    potential_lines = [[],[]]
    retval = starting_y_offset
    lastred1 = 255
    lastred2 = 255
    one_sixth = dpi/6
    one_sixtieth = dpi/60
    one_fiftieth = dpi/50
    if top:
        starty = starting_y_offset
        endy = starty+height_to_scan
        if endy >= image.size[1]: endy = image.size[1]-1
        incr = 1
    else:
        starty = image.size[1] - starting_y_offset
        endy = image.size[1] - starting_y_offset - height_to_scan
        if endy < 0: endy = 0
        incr = -1
    #pretest for one pixel (confirm this gives speedup or remove)
    adj_start = starty
    for y in range(starty,endy,incr):
        p = image.getpixel((starting_x_offset,y))
        if p[0] <= const.line_darkness_threshold:
            adj_start = y - incr
            break
    starty = adj_start

    if (
        starting_x_offset < (2*one_sixth) 
        or starting_x_offset > (image.size[0] - (2*one_sixth))
        ):
        raise LineUtilException("Starting x offset for line following is too close to edge of image.")
    #main test
    for y in range(starty,endy,incr):
        y1 = min(y,y+incr+incr)
        y2 = max(y,y+incr+incr)
        croplist1 = (starting_x_offset - 2*one_sixth,
                    y1,
                    starting_x_offset - one_sixth,
                    y2)
        croplist2 = (starting_x_offset + one_sixth,
                    y1,
                    starting_x_offset + 2*one_sixth,
                    y2)
        crop1 = image.crop(croplist1)
        stat1 = ImageStat.Stat(crop1)
        crop2 = image.crop(croplist2)
        stat2 = ImageStat.Stat(crop2)
        thisred1 = int(stat1.mean[0])
        thisred2 = int(stat2.mean[0])
        # a line must be in the bottom half of intensity and should
        # be substantially darker than the area just before; how substantial
        # will be a tuned value, trying 32 for starters
        if (abs(thisred1-lastred1) > 32 
            and thisred1 < const.line_darkness_threshold):
            potential_lines[0].append(y)
        lastred1 = thisred1
        if (abs(thisred2-lastred2) > 32 
            and thisred2 <= const.line_darkness_threshold):
            potential_lines[1].append(y)
        lastred2 = thisred2
    found = False
    for a in potential_lines[0]:
        for b in potential_lines[1]:
            if abs(a-b) <= one_fiftieth:
                if(lines_connect( image,
                                  (starting_x_offset - one_sixth,a),
                                  (starting_x_offset + one_sixth,b)
                                  )):
                    retval = (a+b)/2
                    #print "Found line btn ",a,b
                    found = True
                    break
            #print a,b,found
        if found: break
    if not found:
        return 0
    return retval

def scan_strip_for_dash_y(image,dpi,starting_x_offset, starting_y_offset=150,height_to_scan=300,top=True):
    """ Scan inboard for a sharp drop in avg intensity of center 1/3 inch.

    Dash detection is a search for a sharp drop in the average intensity
    of a near-center 1/6" by 1/20" region
    from starting_y_offset pixels inboard for height to scan.
    The result of the sharp intensity drop must be below half intensity.
    """
    retval = starting_y_offset
    lastred1 = 255
    one_sixth = dpi/6
    one_sixtieth = dpi/60
    if top:
        starty = starting_y_offset
        endy = starty+height_to_scan
        if endy >= image.size[1]: endy = image.size[1]-1
        incr = 1
    else:
        starty = image.size[1] - starting_y_offset
        endy = image.size[1] - starting_y_offset - height_to_scan
        if endy < 0: endy = 0
        incr = -1
    # we are checking for dashes and must make sure we don't fall through
    # an "undashed" part by checking two regions .1" apart
    #pretest for one pixel (confirm this gives speedup or remove)
    adj_start = starty
    ldt = const.line_darkness_threshold
    for y in range(starty,endy,incr):
        p1 = image.getpixel((starting_x_offset,y))
        p2 = image.getpixel((starting_x_offset+(dpi/10),y))
        if p1[0] <= ldt or p2[0] <= ldt:
            adj_start = y - incr
            break
    starty = adj_start

    #main test; we will span 1/4" which should result in including a full dash
    test_height = (incr*dpi)/100
    for y in range(starty,endy,test_height):
        y1 = min(y,y+test_height)
        y2 = max(y,y+test_height)
        croplist1 = (starting_x_offset,
                    y1,
                    starting_x_offset + (dpi/4),
                    y2)
        crop1 = image.crop(croplist1)
        stat1 = ImageStat.Stat(crop1)
        thisred1 = int(stat1.mean[0])
        # a dash must be in the bottom half of intensity and should
        # be substantially darker than the area just before; how substantial
        # will be a tuned value, trying 32 for starters
        if (abs(thisred1-lastred1) > 32 
            and thisred1 <= const.line_darkness_threshold):
            retval = y
            break
        lastred1 = thisred1
    return retval

def find_all_horiz_lines(image,dpi):
    """ Find all horizontal lines spanning image from 1" down to 1/2" from bot 

    with assumption that an hline is very horizontal, with a sharp light/dark
    intensity boundary spanning an inch on the right
    """
    pot_hlines = []
    center = image.size[0]/2
    half_inch = dpi/2
    lastred = 255
    skip = 0
    ldt = const.line_darkness_threshold
    let = const.line_exit_threshold
    for y in range((dpi/2),image.size[1]-(dpi/2),1):
        if skip > 0: 
            skip -= 1
            continue
        crop = image.crop((image.size[0]-dpi, y, image.size[0], y+1))
        stat = ImageStat.Stat(crop)
        red = stat.mean[0]
        if red <= ldt and lastred >= let and (lastred-red)>32:
            pot_hlines.append(y)
            # count on lines being separated by at least 1/36"
            skip = dpi/36
        lastred = red
    return pot_hlines

if __name__ == "__main__":
    if len(sys.argv) < 3:
        print "usage: python line_util.py image.jpg dpi"
        sys.exit(0)
    image = Image.open(sys.argv[1])
    dpi = int(sys.argv[2])
    print "Starting 5 x hline_split"
    for x in range(5):
        tiltinfo = []
        hline = scan_strips_for_horiz_line_y(image, dpi, 2*dpi, dpi/2, dpi/2,True)
        tiltinfo.append(follow_hline_to_corner(image, dpi, 2*dpi, hline, True))
        hline = scan_strips_for_horiz_line_y(image, dpi, 6*dpi, dpi/2, dpi/2, True)
        tiltinfo.append(follow_hline_to_corner(image, dpi, 6*dpi, hline, False))
        hline=scan_strips_for_horiz_line_y(image, dpi, 6*dpi, dpi/2, dpi/2, False)
        tiltinfo.append(follow_hline_to_corner(image, dpi, 6*dpi, hline, False))
        hline=scan_strips_for_horiz_line_y(image, dpi, 2*dpi, dpi/2, dpi/2, False)
        tiltinfo.append(follow_hline_to_corner(image, dpi, 2*dpi, hline, True))
    for x in range(5):
        tiltinfo = []
        hline = find_hline(image, dpi, 2*dpi, dpi/2, True)
        tiltinfo.append(follow_hline_to_corner(image, dpi, hline, True))
        hline = find_hline(image, dpi, 6*dpi, dpi/2, True)
        tiltinfo.append(follow_hline_to_corner(image, dpi, hline, False))
        hline=find_hline(image, dpi, 2*dpi, dpi/2, False)
        tiltinfo.append(follow_hline_to_corner(image, dpi, hline, False))
        hline=find_hline(image, dpi, 6*dpi, dpi/2, False)
        tiltinfo.append(follow_hline_to_corner(image, dpi, hline, True))
    pot_hlines = find_all_horiz_lines(image,dpi)
    sys.exit(0)
