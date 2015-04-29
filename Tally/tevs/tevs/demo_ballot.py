# demo_ballot.py implements the interface 
# in Ballot.py, as a guide to those extending TEVS to new ballot types.
# The Trachtenberg Election Verification System (TEVS)
# is copyright 2009, 2010 by Mitch Trachtenberg 
# and is licensed under the GNU General Public License version 2.
# (see LICENSE file for details.)


import Ballot
import const
from adjust import rotator

from demo_utils import *

class DemoBallot(Ballot.Ballot):
    """Class representing demonstration ballots.

    Each demonstration ballot's layout code, and contest and choice locations
    are entered by the user through a text interface.

    Precinct code can be any number from 1 to 100.

    The file name demo_ballot.py and the class name DemoBallot
    correspond to the brand entry in tevs.cfg (demo.cfg), 
    the configuration file.

    The only responsibility of a vendor ballot class is to take a set of
    scanned ballot images and construct a template for Ballot.Ballot. There is
    no need to do anything else and doing anything else may result in undefined
    behavior.
    """

    def __init__(self, images, extensions):
        super(DemoBallot, self).__init__(images, extensions)
        print "Creating a Ballot object with", images
        #convert all our constants to locally correct values
        # many of these conversions will go to Ballot.py,
        # extenders will need to handle any new const values here, however
        # add these margins to the vote target's bounding box 
        # when cropping and analyzing for votes
        adj = lambda f: int(round(const.dpi * f))
        self.min_contest_height = adj(const.minimum_contest_height_inches)
        self.vote_target_horiz_offset = adj(const.vote_target_horiz_offset_inches)
        self.writein_xoff = adj(-2.5) #XXX
        self.writein_yoff = adj(-.1)
        self.allowed_corner_black = adj(const.allowed_corner_black_inches)
        super(DemoBallot, self).__init__(images, extensions)

    # Extenders do not need to supply even a stub flip
    # because flip in Ballot.py will print a stub message in the absence
    # of a subclass implementation
    def flip(self, im):
        # not implemented for Demo
        print "In flip"
        return im

    def find_landmarks(self, page):
        """ retrieve landmarks for a demo template, set tang, xref, yref

        Landmarks for the demo ballot are normally at 1/2" down and
        1" in from the top left and top right corners.

        The "image" you are using as a template may be offset or 
        tilted, in which case that information will be recorded
        so it may be taken into account when future images are
        examined.
        """
        print "In find_landmarks"
        a = ask("""Enter the x coordinate of an upper left landmark;
if your template is not offset or tilted, you could use 150.  If there's no
such landmark, enter -1:
""", int, -1)
        b = ask("""Now enter the corresponding y coordinate;
if your template is not offset or tilted, you could use 75.  If there's no
such landmark, enter -1:
""", int, -1)
        c = ask("""Enter the x coordinate of an upper RIGHT landmark;
if your template is not offset or tilted, you could use 2050.  If there's no
such landmark, enter -1:
""", int, -1)
        d = ask("""Enter the corresponding y coordinate;
if your template is not offset or tilted, you could use 75.  If there's no
such landmark, enter -1:
""", int, -1)
        if -1 in (a, b, c, d):
            raise Ballot.BallotException("Could not find landmarks")

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
            avg_darkness = ask(
                "What's the intensity at the " + corner,
                IntIn(0, 255)
            )
            if int(avg_darkness) < 16:
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

        return rot, xoff, yoff, longdiff 

    def get_layout_code(self, page):
        """ Determine the layout code by getting it from the user

        The layout code must be determined on a vendor specific basis;
        it is usually a series of dashes or a bar code at a particular
        location on the ballot.

        Layout codes may appear on both sides of the ballot, or only
        on the fronts.  If the codes appear only on the front, you can
        file the back layout under a layout code generated from the
        front's layout code.
        """
        print "In get_layout_code"
        barcode = ask("""Enter a number as the simulated barcode,
        or -1 if your ballot is missing a barcode""", IntIn(0, 100), -1)
        # If this is a back page, need different arguments
        # to timing marks call; so have failure on front test
        # trigger a back page test
        if barcode == -1:
            raise Ballot.BallotException("No barcode found")
        page.barcode = barcode
        return barcode

    def extract_VOP(self, page, rotatefunc, scale, choice):
        """Extract a single oval, or writein box, from the specified ballot.
        We'll tell you the coordinates, you tell us the stats.  The
        information gathered should enable the IsVoted function to 
        make a reasonable decision about whether the area was voted,
        but the data is also available to anyone else wanting to see
        the raw statistics to make their own decision.
        """
        print "In extract_VOP"
        adj = lambda f: int(round(const.dpi * f))
        iround = lambda x: int(round(x))
        # choice coords should be the upper left hand corner 
        # of the bounding box of the printed vote target
        adj = lambda f: int(round(const.dpi * f))
        x, y = choice.coords()
        x = int(x)
        y = int(y)
        margin_width = page.margin_width
        margin_height = page.margin_height

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

        ow, oh = page.target_width,page.target_height

        print """At %d dpi, on a scale of 0 to 255, 
tell us the average intensity from (%d, %d) for width %d height %d, 
given an offset from the specified x of %d
""" % (const.dpi, x, y, ow, oh, self.vote_target_horiz_offset)
        intensity = ask("Intensity", IntIn(0, 255))
        lowest = ask("Lowest count", IntIn(0, 1000))
        low = ask("Low count", IntIn(0, 1000))
        high = ask("High count", IntIn(0, 1000))
        highest = ask("Highest count", IntIn(0, 1000))
        suspicious = ask("Value of suspicious", int)
        ari, agi, abi  = intensity, intensity, intensity
        lowestr, lowestg, lowestb = lowest, lowest, lowest
        lowr, lowg, lowb = low, low, low
        highestr, highestg, highestb = highest, highest, highest
        highr, highg, highb = high, high, high
        stats = Ballot.IStats(
(ari, lowestr, lowr, highr, highestr,
agi, lowestg, lowg, highg, highestg,
abi, lowestb, lowb, highb, highestb, x, y, 0)
        )

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
            print "Gather information about the write-in at",
            print cropx - margin_width, cropy - margin_height,
            print cropx + self.writein_xoff + margin_width,
            print cropy + self.writein_yoff + margin_height

        return cropx, cropy, stats, crop, voted, writein, ambiguous

    def build_layout(self, page):
        """ get layout and ocr information from Demo ballot

        Building the layout will be the largest task for registering
        a new ballot brand which uses a different layout style.

        Here, we'll ask the user to enter column x-offsets, 
        then contests and their regions,
        and choices belonging to the contest.
        """
        print """Entering build_layout.

You will need to provide a comma separated list of column offsets,
then you will need to provide, for each column, information about
each contest in that column: its contest text, its starting y offset,
and the same for each choice in the contest.
"""
        regionlist = []
        n = 0
        columns = ask(
            """Enter the column offsets of the vote columns, separated by commas""",
            CSV(int)
        )
        for cnum, column in enumerate(columns):
            print "Contests for Column", cnum, "at x offset", column
            while True:
                contest = ask("""Enter a contest name.  When done entering contests, \ntype 'x' and the <enter> key to continue.""")
                if contest.strip().lower() == "x":
                    break
                choices = ask("Enter a comma separated list of choices",
                    CSV())
                # values are the x1,y1,x2,y2 of the bounding box of the contest
                # bounding box, 0 for regular contest or 1 for proposition,
                # and the text of the contest; we'll just dummy them here
                regionlist.append(Ballot.Contest(column, 1, 199, 5*const.dpi, 0, contest))
                for choice in choices:
                    x_offset = ask("Enter the x offset of the upper left hand corner \nof the printed vote target for " + choice, int)
                    y_offset = ask("Enter the y offset of the upper left hand corner \nof the printed vote target for " + choice, int)
                    # values are the x,y of the upper left corner
                    # of the printed vote opportunity, 
                    # and the text of the choice
                    #TODO add x2,y2
                    regionlist[-1].append(Ballot.Choice(x_offset, y_offset, choice))
        return regionlist

