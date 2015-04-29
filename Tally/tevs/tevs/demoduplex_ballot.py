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

class DemoduplexBallot(Ballot.DuplexBallot):
    """Class representing demonstration duplex ballots.

    Each ballot's layout code, and contest and choice locations for each side
    are entered by the user through a text interface.

    Precinct code can be any number from 1 to 100.

    The file name demoduplex_ballot.py and the class name DemoduplexBallot
    correspond to the brand entry in tevs.cfg (demo.cfg), 
    the configuration file.

    The only responsibility of a vendor ballot class is to take a set of
    scanned ballot images and construct a template for Ballot.Ballot. There is
    no need to do anything else and doing anything else may result in undefined
    behavior.
    """

    def __init__(self, images, extensions):
        print "Creating a DuplexBallot with", images
        #convert all our constants to locally correct values
        # many of these conversions will go to Ballot.py,
        # extenders will need to handle any new const values here, however
        adj = lambda f: int(round(const.dpi * f))
        self.min_contest_height = adj(const.minimum_contest_height_inches)
        self.vote_target_horiz_offset = adj(const.vote_target_horiz_offset_inches)
        self.writein_xoff = adj(-2.5) #XXX
        self.writein_yoff = adj(-.1)
        self.allowed_corner_black = adj(const.allowed_corner_black_inches)
        super(DemoduplexBallot, self).__init__(images, extensions)

    #NEVER override this: ONLY overridden so we can add a print trace
    def _swap(self, page): 
        print "\nSWAPPING IMAGES\n"
        return super(DemoduplexBallot, self)._swap(page)

    def flip_front(self, im):
        print "In flip_front"
        return im
    
    def flip_back(self, im):
        print "In flip_back"
        return im

    def is_front(self, im):
        print "In is_front"
        return True

    def find_back_landmarks(self, page):
        print "In find_back_landmarks"
        print_spiel()
        print "Following the default, we simply call find_front_layout from here"
        return self.real_find_front_landmarks(page) #to skip spiel

    def find_front_landmarks(self, page):
        print "In find_front_landmarks"
        print """ retrieve landmarks for a demo template, set tang, xref, yref

 Landmarks for the demo ballot are normally at 1/2" down and
1" in from the top left and top right corners.

The "image" you are using as a template may be offset or 
tilted, in which case that information will be recorded
so it may be taken into account when future images are
examined.
        """
        print "Note that if no front landmarks are found that DuplexBallot"
        print "will swap the images and you'll be asked for this information"
        print "again and if none are found than it will raise an error"
        return self.real_find_front_landmarks(page) #only so we don't repeat^

    def real_find_front_landmarks(self, page):
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
        print "In get_layout_code"
        print """ Determine the layout code by getting it from the user

The layout code must be determined on a vendor specific basis;
it is usually a series of dashes or a bar code at a particular
location on the ballot.

Layout codes may appear on both sides of the ballot, or only
on the fronts.  If the codes appear only on the front, you can
file the back layout under a layout code generated from the
front's layout code.  """
        print "In get_layout_code. Note that DuplexBallot only calls this for"
        print "the first in a pair of images."
        print "Note that if there's no barcode that DuplexBallot will attempt"
        print "to swap the front and back pages and you will be asked again"
        print "and if you still say there is no barcode, an error will be"
        print "raised"
        barcode = ask("""Enter a number as the simulated barcode,
        or -1 if your ballot is missing a barcode""", IntIn(0, 100), -1)
        # If this is a back page, need different arguments
        # to timing marks call; so have failure on front test
        # trigger a back page test
        if barcode == -1:
            raise Ballot.BallotException("No barcode on front page of duplex ballot")
        page.barcode = barcode
        return barcode

    def extract_VOP(self, page, rotatefunc, scale, choice):
        print "In extract_VOP"
        print"""Extract a single oval, or writein box, from the specified ballot.
We'll tell you the coordinates, you tell us the stats.  The
information gathered should enable the IsVoted function to 
make a reasonable decision about whether the area was voted,
but the data is also available to anyone else wanting to see
the raw statistics to make their own decision.  """
        # choice coords should be the upper left hand corner 
        # of the bounding box of the printed vote target
        adj = lambda f: int(round(const.dpi * f))
        iround = lambda x: int(round(x))
        x, y = choice.coords()
        x = int(x)
        y = int(y)

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

        # this is the size of the printed vote target's bounding box

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
            cropx - page.margin_width,
            cropy - page.margin_height,
            cropx + page.margin_width + page.target_width, 
            cropy + page.margin_height + page.target_height
        ))

        #can be in separate func?
        
        voted, ambiguous = self.extensions.IsVoted(crop, stats, choice)
        writein = False
        if voted:
           writein = self.extensions.IsWriteIn(crop, stats, choice)
        if writein:
            print "Gather information about the write-in at",
            print cropx - page.margin_width, cropy - page.margin_height,
            print cropx + self.writein_xoff + page.margin_width,
            print cropy + self.writein_yoff + page.margin_height

        return cropx, cropy, stats, crop, voted, writein, ambiguous

    def build_back_layout(self, page):
        print "Entering build back layout."
        print_spiel()
        print "Following the default, we simply call build_front_layout"
        print "from here."
        print "In build front layout"
        return self.real_build_front_layout(page) #to skip spiel

    def build_front_layout(self, page):
        print """Entering build_front_layout.
get layout and ocr information from Demo ballot

Building the layout will be the largest task for registering
a new ballot brand which uses a different layout style.

Here, we'll ask the user to enter column x-offsets, 
then contests and their regions,
and choices belonging to the contest.

You will need to provide a comma separated list of column offsets,
then you will need to provide, for each column, information about
each contest in that column: its contest text, its starting y offset,
and the same for each choice in the contest.
"""
        return self.real_build_front_layout( page) #so we skip this spiel

    def real_build_front_layout(self, page):
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

def print_spiel():
    print "It will rarely need to be overridden. It's most likely"
    print "that a pair of images will have similiar enough layouts."
    print "And only differ in landmarks and the lack of a unique layout"
    print "code for the backside of ballot images."
