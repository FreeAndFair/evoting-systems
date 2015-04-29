import Ballot
import Image
import ocr
import pdb
import sys
import logging
from line_util import *
from hart_util import *

def hart_build_contests(image, pot_hlines, vboxes, column_start, column_width, dpi=300,extensions=None):
    """Merge horiz lines and vote boxes to get contests and choice offsets."""
    regionlist = []
    contest_description_zones = []
    last_contest = 0
    first_above = 0
    for vbox in vboxes:
        vbox_y = vbox[1]
        for hline in pot_hlines:
            if hline < vbox_y:
                first_above = hline
        if first_above != last_contest:
            last_contest = first_above
            contest_description_zones.append((first_above,vbox_y))
    #print "Contest description zones",contest_description_zones
    for contest in contest_description_zones:
        # crop
        crop = image.crop((column_start,
                           contest[0],
                           column_start + column_width,
                           contest[1]))
        # get text
        zonetext = ocr.tesseract(crop)
        zonetext = ocr.clean_ocr_text(zonetext)
        # create Contest, append to regionlist
        regionlist.append(Ballot.Contest(column_start,
                                         contest[0],
                                         column_start + column_width,
                                         contest[1],
                                         0,
                                         zonetext))

    contest_description_zones.reverse()
    for vbox in vboxes:
        # locate the last contest description zone above vbox
        # and assign vbox to that contest description zone
        
        for contest in contest_description_zones:
            # first contest above vbox gets vbox as choice
            if contest[0] < vbox[1]:
                #print "Vbox at",vbox[1],"in contest at",contest
                # crop area to right of vbox
                # get and clean text
                crop = image.crop((vbox[0] + dpi/3 + dpi/30, #!!!
                                            vbox[1] - dpi/100, #!!!
                                            vbox[0]+column_width-(dpi/2), #!!!
                                            vbox[1]+(dpi/2)))
                choice_text = ocr.tesseract(crop) #!!!
                # take only first line of choice
                choice_text = ocr.clean_ocr_text(choice_text).split("/")[0]

                # search regionlist for matching Contest, append
                #match.append(Ballot.Choice(...,choice_text))
                for rcontest in regionlist:
                    if rcontest.y == contest[0] and rcontest.x == column_start:
                        rcontest.append(Ballot.Choice(
                                vbox[0],
                                vbox[1],
                                choice_text)
                                        )
                        break
                break
    logger = logging.getLogger('')
    for contest in regionlist:
        logger.info("%d %d %s" % (contest.x, contest.y, contest.description))
        for choice in contest.choices:
            logger.info(" %d %d %s" % (choice.x, choice.y, choice.description))

    return regionlist

if __name__ == "__main__":
    # work through a layout build from a test image at a dpi
    # use .07" as horizontal offset of vote target left edge from column edge
    # assume three columns
    # no use of PILB
    # a ballot image WILL and MUST have been deskewed prior to layout build
    if len(sys.argv)<3: print "usage hart_build_contests imagefile.jpg dpi"
    image = Image.open(sys.argv[1])
    dpi = int(sys.argv[2])
    vthop = int(round(dpi * .07))
    # get landmarks
    TOP=True
    BOT=False
    LEFT=True
    RIGHT=False

    # each of the four box corners is located by scanning to a horizontal line
    # and following it out horizontally until it ends

    # tiltinfo, from upperleft clockwise:
    # [(x,y),(x,y),(x,y),(x,y)] or None
    tiltinfo = []

    # upper left
    hline = scan_strips_for_horiz_line_y(image, 
                                         dpi, 
                                         2*dpi, 
                                         dpi/2, dpi/2,
                                         TOP)
    tiltinfo.append(follow_hline_to_corner(image, 
                                           dpi, 
                                           2*dpi, 
                                           hline, LEFT))

    # upper right
    hline = scan_strips_for_horiz_line_y(image, 
                                         dpi, 
                                         6*dpi, 
                                         dpi/2, dpi/2, 
                                         TOP)
    tiltinfo.append(follow_hline_to_corner(image, 
                                           dpi, 
                                           6*dpi,
                                           hline, RIGHT))

    # lower right
    hline=scan_strips_for_horiz_line_y(image, 
                                       dpi, 
                                       6*dpi, 
                                       dpi/2, dpi/2, 
                                       BOT)
    tiltinfo.append(follow_hline_to_corner(image, 
                                           dpi, 
                                           6*dpi,
                                           hline, RIGHT))

    # lower left
    hline=scan_strips_for_horiz_line_y(image, 
                                       dpi, 
                                       2*dpi, 
                                       dpi/2, dpi/2, 
                                       BOT)
    tiltinfo.append(follow_hline_to_corner(image, 
                                           dpi, 
                                           2*dpi,
                                           hline, LEFT))

    # get vlines, assuming the ballot has three columns
    first_line = tiltinfo[0][0]
    last_line =  tiltinfo[1][0]
    width = last_line - first_line
    first_third = first_line + width/3
    second_third = first_line + (2*width)/3
    print "Warning: assuming three columns"
    print first_line,first_third,second_third,last_line
    vlines = [first_line,first_third,second_third,last_line]
    column_width = width/3

    # for each column, 
    # get horizontal lines, get voteboxes, and build contest/choice tree
    contests = []
    for vline in vlines:
        croplist = (vline,0,vline+column_width,image.size[1])
        crop = image.crop(croplist)
        pot_hlines = find_all_horiz_lines(crop,dpi)
        # normally, pull the .07 from config.vote_box_horiz_offset_inches
        vboxes = gethartvoteboxes(image,vline+vthop,dpi/2,dpi)
        column_contests = hart_build_contests(image,
                                              pot_hlines,
                                              vboxes,
                                              vline,
                                              column_width)
        contests.extend(column_contests)
    for contest in contests:
        print contest.x, contest.y, contest.description
        for choice in contest.choices:
            print " ", choice.x, choice.y, choice.description

        
    # vbox upper left corners at the following coordinates
