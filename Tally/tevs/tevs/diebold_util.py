import Image, ImageStat
import sys
import pdb
import const
import line_util

dark_threshold = 236
light_threshold = 240


def count_lines_without_dark_pixel(im, start_x, start_y, end_x, end_y, thresh):
    """ Return number of lines with no dark pixel from x to x2"""
    dark_misses = 0
    start_y, end_y = min(start_y, end_y), max(start_y, end_y)
    for test_y in range(start_y,end_y):
        found_dark = False
        for test_x in range(start_x,end_x):
            p = im.getpixel((test_x,test_y))
            if p[0] <= thresh:
                found_dark = True
                break
        if not found_dark:
            dark_misses += 1
    return dark_misses

def get_ulc_if_untinted_oval(im, x, y):
    """Return upper left corner of oval bbox if x,y on oval's bottom wall.

    Look back to find trailing oval offering darkness at:

    left wall, up by half oval height and back by half oval width,
    with half oval width of checking;

    right wall, up by half oval height and forward by half oval width,
    with half oval width of checking;

    and top wall, up by oval height with half oval height of checking.
    """
    oval_height = int(round(const.target_height_inches * const.dpi))
    oval_width = int(round(const.target_width_inches * const.dpi))
    left_wall = -1
    exclusion_zone_width = int(round(0.03 * const.dpi))
    mid_oval_y = int(round(y - (oval_height/2)))
    top_oval_y = y - oval_height
    for test_x in range(x-oval_width,x):
        p = im.getpixel((test_x,mid_oval_y))
        if p[0]<=dark_threshold:
            # first check: confirm at least one dark pixel
            # on each line from mid_oval to bottom and top of oval,
            # going out from test_x to test_x + mid_oval
            dark_misses = count_lines_without_dark_pixel(
                im,
                test_x,
                top_oval_y,
                test_x + int(round(oval_height/2)),
                y,
                dark_threshold)
            if dark_misses > 1:
                continue
            # confirm average intensity in exclusion zone > light_threshold
            xzone_stat = ImageStat.Stat(im.crop((test_x - exclusion_zone_width,
                                                 mid_oval_y,
                                                 test_x - 1,
                                                 mid_oval_y+1)))
            if xzone_stat.mean[0] >= light_threshold:
                left_wall = test_x
                break
    
    if left_wall < 0:return []

    right_wall = -1
    # now that we've found a left wall, anticipate the right wall 
    # at left_wall + oval_width
    for test_x in range(left_wall+oval_width-(const.dpi/32),
                        left_wall+oval_width+(const.dpi/32)):
        p = im.getpixel((test_x,mid_oval_y))
        if p[0] <= dark_threshold:
            # first check: confirm at least one dark pixel
            # on each line from mid_oval to bottom and top of oval,
            # going out from test_x to test_x + mid_oval
            dark_misses = count_lines_without_dark_pixel(
                im,
                test_x - (oval_height/2),
                top_oval_y,
                test_x ,
                y,
                dark_threshold)
            if dark_misses > 1:
                continue
            # confirm average intensity in exclusion zone > light_threshold
            xzone_stat = ImageStat.Stat(im.crop((test_x + 1,
                                                 mid_oval_y,
                                                 test_x + exclusion_zone_width,
                                                 mid_oval_y+1)))
            if xzone_stat.mean[0] >= light_threshold:
                right_wall = test_x
                break

    if left_wall < 0 or right_wall < 0:
        return []

    top_wall = -1
    for test_y in range(y - (3*oval_height/2),y-(oval_height/2),1):
        p = im.getpixel((x,test_y))
        if p[0]<dark_threshold: 
            # confirm average intensity in exclusion zone > light_threshold
            xzone_stat = ImageStat.Stat(im.crop((x,
                                                 test_y - exclusion_zone_width,
                                                 x + exclusion_zone_width,
                                                 test_y - 1)))
            if xzone_stat.mean[0] >= light_threshold:
                top_wall = test_y
                break
    if left_wall >= 0 and right_wall >= 0 and top_wall >=0:
        return [left_wall,top_wall]
    else:
        return []


def find_bottom_landmark_dash(page,starting_x,starting_y,dpi):
    """ Return x offset of inboard edge of dash at starting_y.

        Unfortunately, a bottom dash might stand alone, so we must start
        looking close to the edge and eliminate the requirement to pass a 
        dark pixel before finding a white/black boundary.


        It's not in a dash unless it is dark with white above and below.
        Wait to be in a dash and then return first x not in a dash.
    """
    # simplify testing by taking page argument as image if no image attr
    return_x = -1
    try:
        im = page.image
    except:
        im = page
    if starting_x < (im.size[0]/2):
        # go from starting point rightwards
        incr = 1
    else:
        # go from starting point leftwards
        incr = -1
    # skip pixels until dark pixel is found with white above and below
    ldt = const.line_darkness_threshold
    let = const.line_exit_threshold
    for test_x in range(starting_x,starting_x + (incr*dpi/4),incr):
        p = im.getpixel((test_x,starting_y))
        p_above = im.getpixel((test_x,starting_y - (dpi/10)))
        p_below = im.getpixel((test_x,starting_y + (dpi/10)))
        if p[0] <= ldt and p_above[0] >= let and p_below >= let:
            starting_x = test_x
            break
        else:
            continue
        break
    # now scan all black pixels, breaking at first white, which is landmark
    for test_x in range(starting_x+incr,starting_x + (incr*dpi/4),incr):
        p = im.getpixel((test_x,starting_y))
        if p[0] >= const.line_darkness_threshold:
            return_x = test_x 
            break
    return return_x


def find_top_landmark_dash(page, starting_x, starting_y, dpi):
    """ Return x offset of inboard edge of dash at starting_y.

        For top dashes, we can start in what would be the second dash
        and insist on traveling through some black before resetting on
        white and looking for black again.  Then, if we are more than 1/4"
        from the edge, we can check 1/4" farther to the edge and see if 
        there's another black pixel there bounded by white pixels above 
        and below, in which case the black pixel at the edge is the location
        we want.

        Unfortunately, a bottom dash might stand alone, so we must start
        looking close to the edge and eliminate the requirement to pass a 
        dark pixel before finding a white/black boundary.
    """
    oval_height = int(round(const.target_height_inches * dpi))
    oval_width = int(round(const.target_width_inches * dpi))
    return_x = -1
    # simplify testing by taking page argument as image if no image attr
    try:
        im = page.image
    except:
        im = page
    if starting_x < (im.size[0]/2):
        # go from starting point leftwards
        incr = -1
        ending_x = 1
    else:
        # go from starting point rightwards
        incr = 1
        ending_x = im.size[0] - 1

    # we must pass through a dark pix followed by >= dpi/50 light pix,
    # then stop at next dark pix; if that location is > dpi/4, 
    # check to see if pix at location - dpi/4 is dark 
    # and positions 1/10" above and below are light; if so,
    # subtract dpi/4 from returned x coordinate.
    passed_dark_pix = False
    num_light_pix = 0
    required_light_pix = dpi/50
    landmark_x = -1
    for test_x in range(starting_x, ending_x, incr):
        pix = im.getpixel((test_x,starting_y))
        dark = (pix[0] <= const.line_darkness_threshold)
        if dark:
            passed_dark_pix = True
            num_light_pix = 0
        elif passed_dark_pix:
            num_light_pix += 1
            if num_light_pix > required_light_pix:
                landmark_x = test_x
                break
    # continue in same direction until dark encountered again
    for test_x in range(landmark_x, ending_x, incr):
        pix = im.getpixel((test_x,starting_y))
        if pix[0] <= const.line_darkness_threshold:
            landmark_x = test_x - incr
            break

    # go with more extreme alternative if it has a dash
    if landmark_x > (1+(dpi/4)) and landmark_x < (im.size[0]-(1+(dpi/4))):
        alternate_x = test_x + incr*(1+(dpi/4))
        p = im.getpixel((alternate_x,starting_y))
        p_above = im.getpixel((alternate_x,starting_y-(dpi/10)))
        p_below = im.getpixel((alternate_x,starting_y+(dpi/10)))
        darkp = (p[0] < const.line_darkness_threshold)
        darkp_above = (p_above[0] < const.line_darkness_threshold)
        darkp_below = (p_below[0] < const.line_darkness_threshold)
        if darkp and ((not darkp_above) or (not darkp_below)):
            landmark_x = alternate_x
    return landmark_x

def find_horizontal_lines(page, starting_x, dpi):
    retlist = []
    # simplify testing by taking page argument as image if no image attr
    try:
        im = page.image
    except:
        im = page
    starting_y_offset = 300
    while True:
        line =line_util.scan_strips_for_horiz_line_y(
            im,
            dpi,
            starting_x,
            starting_y_offset = starting_y_offset, 
            height_to_scan=(im.size[1] - starting_y_offset - (dpi/4)))
        #print "Line at",line
        if line == 0: 
            break
        else: 
            retlist.append(line) 
            starting_y_offset = line+(dpi/6)
    #print "Line list",retlist
    return retlist

def find_potential_contests(lines,min_sep):
    """Two lines must be separated by >= min_sep to be contest bounds."""
    pot_contests = []
    lines2 = lines[1:]
    #lines2.append(lines[-1])
    for a,b in zip(lines,lines2):
        a,b = min(a,b), max(a,b)
        if (b-a) >= min_sep:
            pot_contests.append((a,b))
    return pot_contests

def find_untinted_voteops(page,starting_x,starting_y,ending_y,dpi):
    """Given deskewed image and starting x, return list of untinted voteops.

    The Humboldt Diebold images are so compressed that the tint is iffy.

    The SLO Diebold images use untinted vote ovals.

    So an alternative is to use a darkness test followed by a check for
    darkness at the correct related pixels, COUPLED WITH A TEST FOR 
    NO SUBSTANTIAL DARKNESS IN TEST ZONES OUTBOARD FROM THE OVAL. 

    Scan down deskewed image at starting x.

    When tinted pixel found, call is_bottom_wall_of_oval to determine
    existence of vote oval ending at coords.

    When only one oval is found in a sublist, 
    check for additional oval at same y offset

    """
    oval_height = int(round(const.target_height_inches * dpi))
    oval_width = int(round(const.target_width_inches * dpi))
    retlist = []
    # simplify testing by taking page argument as image if no image attr
    try:
        im = page.image
    except:
        im = page
    skip = 0
    for y in range(starting_y,ending_y,1):
        if skip > 0:
            skip -= 1
            continue
        p = im.getpixel((starting_x,y))
        # on darkened pix, check for and append oval to retlist
        ulc_of_oval = []
        if p[0] < dark_threshold:
            # first check a horizontal line to confirm multiple darks
            crop = im.crop((int(starting_x - 10),
                               int(y),
                               int(starting_x + 10),
                               int(y+1)))
            mean = ImageStat.Stat(crop).mean[0]
            #print "Croplist",starting_x -10,y,starting_x+10,y+1,"mean red",mean
            if mean > 240:
                continue
            #print "Checking at", starting_x, y
            ulc_of_oval = get_ulc_if_untinted_oval(im,starting_x,y)
            if len(ulc_of_oval)<1:
                continue
            # you could OCR now and store Choices instead of coords
            retlist.append(ulc_of_oval)
            # if you add an oval, you can skip dpi/6 pixels, because
            # ovals will never be spaced closer than 1/6" apart
            skip = dpi/6
    #print "Retlist",retlist
    #pdb.set_trace()
    if len(retlist)!=1:
        return retlist
    # where only one oval has been located
    # search for a second vote oval horizontal-aligned with the first
    # we assume column width of not more than 2.75",
    # and further assume ovals aligned on quarter inch horiz 
    # and further assume horizontally oriented ovals will not be
    # closer than 3/4" apart
    # Use the one and only y coordinate in the single entry retlist

    # Beware of drift due to tilt; may need to test several y's
    for y in range(retlist[0][1] + oval_height-2,
                   retlist[0][1] + oval_height + 2):
        # if another oval has been appended in the loop, break
        if len(retlist) > 1:
            break
        for n in range(3,8):
            test_x = starting_x + ((n*dpi)/4)
            p = im.getpixel((test_x,y))
            # on tinted pix, check for and append oval to current sublist;
            # on darkened untinted pix, add new sublist
            ulc_of_oval = []
            if p[0] < dark_threshold:
                # first check a horizontal line to confirm multiple darks
                croplist = (test_x - 10,
                            y,
                            test_x + 10,
                            y+1)
                crop = im.crop(croplist)
                mean = ImageStat.Stat(crop).mean[0]
                if mean > 240:
                    continue
                ulc_of_oval = get_ulc_if_untinted_oval(im,test_x,y)
                if len(ulc_of_oval)<1:
                    continue
                retlist.append(ulc_of_oval)
                break

    return retlist


if __name__ == "__main__":
    if len(sys.argv) < 3:
        print "usage: python diebold_util.py diebold_image_filename startx"
    image = Image.open(sys.argv[1])
    startx = int(sys.argv[2])
    starting_y_offset = 300
    lines = find_horizontal_lines(image,startx,dpi)
    pot_contests = find_potential_contests(lines,150)
    print pot_contests
    for contest_start_y, contest_end_y in pot_contests:
        print "Searching targets from y to y",contest_start_y, contest_end_y
        vops = find_untinted_voteops(image,
                                     startx,
                                     contest_start_y,
                                     contest_end_y,
                                     dpi)
        print "Found",vops
    sys.exit(0)
