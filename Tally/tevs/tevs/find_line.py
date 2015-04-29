# Find the first boundary/line below a given point, and return its endpoints.
import Image
import sys
import pdb
"""
Starting at startx,starty, search downwards and rightwards pixel by pixel
for search_npixels, until there is an intensity difference > threshold
between the current pixel and that two beneath (to allow for 
partial coloration at boundary).  This becomes a candidate point;
check every stride pixels rightward and leftward at that vertical offset +/- 1
to see if there is a similar boundary.  

At each confirmed boundary point, readjust vertical offset if
boundary has slipped up or down by one.  

If line's x span exceeds the required length, return the line's end point
coordinates; otherwise, keep trying additional candidate points.

If no line is found within specified search region, return None.
"""


class NoLineException(Exception):
    pass
class BadBlockSeedException(Exception):
    pass

def difference_exceeds_threshold(p1, p2, threshold):
    """return whether avg diff across colors exceeds spec'd threshold"""
    return (abs(p1[0]-p2[0])
            + abs(p1[1]-p2[1]) 
            + abs(p1[2]-p2[2])) > (3 * threshold)

def boundary_test(im, x, y, threshold, search_inc=1, black_sufficient=False):
    """return required v adj to stay at boundary, or None if off boundary"""
    # search_inc controls whether we search for a boundary
    # above our test pixel or below our test pixel
    # or with one two below

    # the adjustments by 2 turn out to be necessary to avoid
    # premature termination of the line in certain circumstances
    for adj in (0, -1, 1, -2, 2):
        try:
            p0 = im.getpixel((x,y+adj))
            p1 = im.getpixel((x,y+(2*search_inc)+adj))
            d = difference_exceeds_threshold(p0,p1,threshold)
            if d is True:
                return adj
        except IndexError:
            continue
    # this should never be reached, but is included just in case 
    # a single pixel thick line is encountered
    for adj in (0, -1, 1, -2, 2):
        try:
            p0 = im.getpixel((x,y+adj))
            p1 = im.getpixel((x,y+(1*search_inc)+adj))
            d = difference_exceeds_threshold(p0,p1,threshold)
            if d is True:
                return adj
        except IndexError:
            continue
    # if the boundary is a black line and there is black on the approach
    # (from, for example, a region with a black block meeting the line)
    # we need an option to count black as acceptable
    if black_sufficient:
        try:
            p0 = im.getpixel((x,y))
            p1 = im.getpixel((x,y+1))
            p2 = im.getpixel((x,y+2))
            if (    (p0[0]+p0[1]+p0[2] < (threshold*3))
                and (p1[0]+p1[1]+p1[2] < (threshold*3))
                and (p2[0]+p2[1]+p2[2] < (threshold*3)) ):
                return 0
        except IndexError:
            pass
    return None

def point_to_line(im, 
                  x, # anchor point x coord
                  y, # anchor point y coord
                  threshold, # how much intensity difference is needed?
                  stride, # how far apart should our initial checks be? 
                  min_length, # what minimum x span is required?
                  allowed_misses=1, # how many "specks" should we accept?
                  search_inc=1, # in which direction do we look for boundary?
                  black_sufficient=False # can "boundary" follow all black?
                  ):
    """return endpoints of nearly horiz line exceeding min_length, or raise"""
    left_misses, right_misses = 0, 0
    current_left_x, current_left_y = x, y
    test_left_x, test_left_y = x, y
    current_right_x, current_right_y = x, y
    test_right_x, test_right_y = x, y
    left_x = None
    right_x = None
    while not (left_misses > allowed_misses and right_misses > allowed_misses):
        if not left_misses > allowed_misses:
            test_left_x = current_left_x - stride
            test_left_y = current_left_y
            if test_left_x < 0:
                left_misses += 1
                test_left_x = 0
            else:
                # search_inc indicates in which direction
                # we are looking for a boundary, which controls
                # whether we compare a given pixel with one two above
                # or the same pixel with one two below
                bt = boundary_test(im, 
                                   test_left_x, 
                                   test_left_y, 
                                   threshold,
                                   search_inc=search_inc,
                                   black_sufficient=black_sufficient)
                if bt is None:
                    left_misses += 1
                else:
                    current_left_y += bt
                    left_misses = 0
            current_left_x = test_left_x
            
        if not right_misses > allowed_misses:
            test_right_x = current_right_x + stride
            test_right_y = current_right_y
            if test_right_x >= im.size[0]:
                right_misses +=1
                test_right_x = im.size[0]-1
            else:
                bt = boundary_test(im, 
                                   test_right_x, 
                                   test_right_y, 
                                   threshold,
                                   search_inc=search_inc,
                                   black_sufficient=black_sufficient)
                if bt is None:
                    right_misses += 1
                else:
                    current_right_y += bt
                    right_misses = 0
            current_right_x = test_right_x
    # while is exited only when both left and right have been approx found
    # the actual boundary end is no more than stride * [left|right]_misses away
    # back up towards starting point and repeat process with stride 1
    current_left_x = max(current_left_x+(stride*left_misses),-1)
    current_right_x = min(current_right_x-(stride*right_misses),im.size[0]-1)
    left_misses, right_misses = 0, 0
    stride = 1
    while not (left_misses > allowed_misses and right_misses > allowed_misses):
        if not left_misses > allowed_misses:
            test_left_x = current_left_x - stride
            test_left_y = current_left_y
            bt = boundary_test(im, 
                               test_left_x, 
                               test_left_y, 
                               threshold,
                               search_inc=search_inc,
                               black_sufficient=black_sufficient)
            if bt is None:
                left_misses += 1
            else:
                current_left_y += bt
                left_misses = 0
            current_left_x = test_left_x
        if not right_misses > allowed_misses:
            test_right_x = current_right_x + stride
            test_right_y = current_right_y
            bt = boundary_test(im, 
                               test_right_x, 
                               test_right_y, 
                               threshold,
                               search_inc=search_inc,
                               black_sufficient=black_sufficient)
            if bt is None:
                right_misses += 1
            else:
                current_right_y += bt
                right_misses = 0
            current_right_x = test_right_x
    # the x's are adjusted back by the miss count
    current_left_x += left_misses
    current_right_x -= right_misses
    line_length = current_right_x - current_left_x
    if line_length < min_length:
        raise NoLineException(line_length)
    # the y's are adjusted up 1 or -1 due to our having tested for intensity
    # difference between y and y+2 or y-2
    return (current_left_x,
            current_left_y+search_inc,
            current_right_x,
            current_right_y+search_inc)


def find_line(image_or_region,
              startx=0, # search start x
              starty=0, # search start y
              search_npixels=300, # may be negative to search up from start y
              threshold=128, # intensity difference required at boundary
              stride=10, # initial sampling frequency at boundary
              min_length=300, 
              allowed_misses=1,
              extend=True,
              black_sufficient=False):
    """return endpt coords of first boundary >= spec'd min_length, or None"""
    im = image_or_region
    # search for candidate transition
    # if the search_npixels is negative, we are searching upwards,
    # using a search_inc(rement) of negative one
    search_inc = search_npixels/abs(search_npixels)
    for x in range(startx,startx+search_npixels,search_inc):
        for y in range(starty,starty+search_npixels,search_inc):
            try:
                p1 = im.getpixel((x,y))
                p2 = im.getpixel((x,y+(2*search_inc)))
            except IndexError:
                continue
            if not difference_exceeds_threshold(p1,p2,threshold):
                continue
            # x,y+1 is a boundary candidate; check
            try:
                return point_to_line(im, 
                                     x, 
                                     y + search_inc, 
                                     threshold, 
                                     stride, 
                                     min_length, 
                                     allowed_misses=allowed_misses,
                                     search_inc = search_inc,
                                     black_sufficient = black_sufficient)
            except NoLineException:
                continue
    return None

def find_block_extents(im, startx, starty, min_darkness=128):
    """return ulc and lrc coords of dark block surrounding start_x, start_y"""
    xinc, xdec, yinc, ydec = 0, 0, 0, 0
    if startx < 0 or startx >= im.size[0] or starty < 0 or starty >= im.size[1]:
        raise BadBlockSeedException((startx,starty))
    while(1):
        if startx+xinc >= im.size[0]:break
        p = im.getpixel((startx+xinc, starty))
        is_dark = ((p[0]+p[1]+p[2]) <= (3*min_darkness))
        if not is_dark: break
        xinc += 1
    while(1):
        if startx-xdec < 0: break
        p = im.getpixel((startx-xdec, starty))
        is_dark = ((p[0]+p[1]+p[2]) <= (3*min_darkness))
        if not is_dark: break
        xdec += 1
    while(1):
        if starty+yinc >= im.size[1]:break
        p = im.getpixel((startx, starty+yinc))
        is_dark = ((p[0]+p[1]+p[2]) <= (3*min_darkness))
        if not is_dark: break
        yinc += 1
    while(1):
        if starty-ydec < 0: break
        p = im.getpixel((startx, starty-ydec))
        is_dark = ((p[0]+p[1]+p[2]) <= (3*min_darkness))
        if not is_dark: break
        ydec += 1
    return (startx-xdec,starty-ydec,startx+xinc,starty+yinc)
    

if __name__=="__main__":
    if len(sys.argv)<2:
        print "Usage: python findline.py testfile.jpg"
        sys.exit(1)
    try:
        im = Image.open(sys.argv[1])
    except Exception as e:
        print "Could not open %s as image." % (sys.argv[1],)
        sys.exit(2)
    line, line2 = None, None
    try:
        line = find_line(im,
                         startx=600,
                         starty=150,
                         search_npixels=300,
                         threshold=128,
                         stride=10,
                         min_length=300,
                         allowed_misses=1)
    except Exception as e:
        print "Exception in call to find_line:"
        print e
        sys.exit(3)
    if line is None: 
        print "No boundary found meeting conditions."
        sys.exit(0)
    print "Line found with endpoints",line
    t = -float(line[3] - line[1])/float(line[2]-line[0])
    print "(For small rotations, tangent = arctangent)"
    print "Tangent (arctangent in radians)", t
    print "Tangent (arctangent as degrees)", t * (180./3.14)
    # on an ESS ballot front, there will be a block preceding the line
    x1,y1,x2,y2 = find_block_extents(im,line[0]-50,line[1]+20)
    print "Block extents around (%d,%d): ULC %d,%d, LRC %d,%d" % (
        line[0]-50,
        line[1]+20,
        x1,y1,x2,y2)
    try:
        find_block_extents(im,-1,0)
    except BadBlockSeedException as e:
        print type(e),e
    try:
        line = find_line(im,
                         startx=600,
                         starty=4100,
                         search_npixels=-300,
                         threshold=128,
                         stride=10,
                         min_length=300,
                         allowed_misses=1)
    except Exception as e:
        print "Exception in call to find_line:"
        print e
        sys.exit(3)
    if line is None: 
        print "No boundary found meeting conditions."
        sys.exit(0)
    print "Line found with endpoints",line
    t = -float(line[3] - line[1])/float(line[2]-line[0])
    print "(For small rotations, tangent = arctangent)"
    print "Tangent (arctangent in radians)", t
    print "Tangent (arctangent as degrees)", t * (180./3.14)
    # on an ESS ballot front, there will be a block preceding the line
    x1,y1,x2,y2 = find_block_extents(im,line[0]-50,line[1]-20)
    print "Block extents around (%d,%d): ULC %d,%d, LRC %d,%d" % (
        line[0]-50,
        line[1]-20,
        x1,y1,x2,y2)
    #rotate by -t degrees to cancel rotation of image
    im = im.rotate(-t * (180./3.14))
    #im.save("/tmp/derotated.jpg")
    im = im.rotate(-90.)
    im.save("/tmp/rotatedneg90.jpg")
    bottomlinestartx = line[0]
    bottomlineendx=line[2]
    bottomlinewidth= line[2]-line[0]
    testloc1 = bottomlinestartx - 50
    testloc2 = bottomlinestartx + (bottomlinewidth/5) - 50
    testloc3 = bottomlinestartx + (bottomlinewidth/4) - 50
    testloc4 = bottomlinestartx + (bottomlinewidth/3) - 50
    testloc5 = bottomlinestartx + (2*bottomlinewidth/5) - 50
    testloc6 = bottomlinestartx + (2*bottomlinewidth/4) - 50
    testloc7 = bottomlinestartx + (2*bottomlinewidth/3) - 50
    testloc8 = bottomlinestartx + bottomlinewidth - 50
    v_offsets = []
    # given derotated image, it should be OK to use black_sufficient,
    # allowing us to capture black line boundaries even when interior
    # parts of them are preceded by black, as:
    #            XXXXXX               
    #            XXXXXX
    # XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
    # XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
    for loc in (testloc1,testloc2,testloc3,testloc4,testloc5,testloc6,testloc7,testloc8):
        x = find_line(im,
                      startx=im.size[0]-line[1]-50,
                      starty=loc,
                      black_sufficient=True)
        print "Column boundary",x
        if x is not None:
            v_offsets.append(x[1]) 
    print "Column x offsets",v_offsets
    for x in range(len(v_offsets)-1):
        diff = v_offsets[x+1]-v_offsets[x]
        if diff > 20: 
            print "Column width",diff
    sys.exit(0)
