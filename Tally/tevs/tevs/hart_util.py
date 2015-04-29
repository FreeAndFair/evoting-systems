import pdb
import sys
import Image

def check_for_votebox_at(image,dpi,x,y):
    """ Given a location with a black pixel, see if there's a votebox.

    Check the next line down and the line 1/7" below 
    to see if you find a pair of dark lines each 1/4" or longer,
    and noting the x at which each of the lines started

    if pass that test, look for vertical connecting lines 1/10" tall or taller
    starting somewhere between startx and startx plus half inch, probably
    at the first point on the dark horizontal lines already found.

    if pass that test, return ulc coordinate pair of presumed box, else 0,0

"""
    y1 = y+1
    y2 = y + (dpi/7)
    dark = 0
    init_x = 0
    hundredth_inch = dpi/100
    quarter_inch = dpi/4
    tenth_inch = dpi/10
    range_start = x
    range_end = int(round(x+(0.3*dpi)))
    for test_x in range(range_start,range_end,1):
        p1 = image.getpixel((test_x,y1))
        p2 = image.getpixel((test_x,y2))
        if p1[0]<128 and p2[0]<128:
            if init_x == 0: init_x = test_x
            dark += 1
            if dark > quarter_inch:
                break
    # fail if you haven't found 1/4" of dark within .3" of expected start
    if dark <= quarter_inch:
        return (0,0)

    # if you've passed, try moving left by up to 1/32" until first white 
    for test_x in range(x,x-(dpi/32),-1):
        p = image.getpixel((test_x,y1))
        if p[0]>128: break
        init_x = test_x
    # and try moving up by up to 1/32" until first white 
    new_y1 = y1
    for test_y in range(y1,y1-(dpi/32),-1):
        p = image.getpixel((init_x,test_y))
        if p[0]>128: break
        new_y1 = test_y
    y1 = new_y1
    
    # check for 1/10" vertical connecting lines
    dark = 0
    init_y = 0
    for test_y in range(y1,y2,1):
        p0 = image.getpixel((init_x-hundredth_inch,test_y))
        p1 = image.getpixel((init_x,test_y))
        p2 = image.getpixel((init_x+hundredth_inch,test_y))
        if p0[0]<128 or p1[0]<128 or p2[0]<128:
            if init_y == 0: init_y = test_y
            dark += 1
            if dark > tenth_inch:
                break
    # fail if you haven't found 1/10" dark within 1/7"
    if dark <= tenth_inch:
        return (0,0)

    # check for 1/10" white before vertical connecting lines
    light = 0
    for test_y in range(y1,y2,1):
        p0 = image.getpixel((init_x-(2*hundredth_inch),test_y))
        if p0[0]>128:
            light += 1
            if light > tenth_inch:
                break
    if light <= tenth_inch:
        return(0,0)

    return (init_x,init_y)

def gethartvoteboxes(image,startx,starty,dpi):
    """
    Build list of ulc of vote target boxes in image near startx.

    This will be called with startx set to each column's starting x
    plus const.vote_target_horiz_offset_inches,
    and should only be called once the image has been deskewed, so 
    we should be able to rely on the vote boxes being at or near
    the specified x.

    scan from starty+1 to a half inch from the bottom looking for
    red intensity <= 128 at startx plus quarter inch

    when found, call check_for_votebox_at 

"""
    hundredth_inch = dpi/100.
    quarter_inch = dpi/4
    minimum_box_top_to_top = dpi/5
    votebox_list = []
    # try searching for votebox at .01" from specified x offset 
    # and .02" from specified x offset; given that our image MUST
    # have been deskewed by this point, this will work
    # unless the image bows out by more than 1/50"
    x = startx + int(round(hundredth_inch))
    x2 = x + int(round(2*hundredth_inch))
    skip = 0
    for y in range(starty+1,image.size[1]-(dpi/2),1):
        if skip>0:
            skip -= 1
            continue
        p = image.getpixel((x,y))
        if p[0]<128:
            a,b = check_for_votebox_at(image,dpi,x,y)
            if a>0 and b>0:
                votebox_list.append((a,b))
                skip = minimum_box_top_to_top
        else:
            p2 = image.getpixel((x2,y))
            if p2[0]<128:
                a,b = check_for_votebox_at(image,dpi,x2,y)
                if a>0 and b>0:
                    votebox_list.append((a,b))
                    skip = minimum_box_top_to_top
    return votebox_list

if __name__ == "__main__":
    if len(sys.argv) < 4:
        print "usage: python hart_util.py image.jpg dpi x_offset"
        sys.exit(0)
    image = Image.open(sys.argv[1])
    dpi = int(sys.argv[2])
    x_offset = int(sys.argv[3])
    ret = gethartvoteboxes(image,x_offset,dpi,dpi)
    print ret
