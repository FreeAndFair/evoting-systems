from PILB import Image, ImageDraw
from util_test import *
import Ballot

class ShillExtensions(object):
    def __init__(self):
        self.transformer = lambda _1, _2, _3: lambda x, y: (x, y)

class ShillBallot(Ballot.Ballot):
    def __init__(self):
        self.min_contest_height = 40
        self.results = []
        self.extensions = ShillExtensions()

    #XXX extract_VOP really really should just be in Ballot
    def extract_VOP(self, page, rotate, scale, choice):
        x, y = choice.x, choice.y
        crop = page.image.crop((x, y, x + 50, y + 50))
        return x, y, None, crop, True, False, False

def CapturePageInfo_test():
    #create fake ballot image
    im = Image.new("RGB", (100, 400), "white")
    d = ImageDraw.Draw(im)
    #list of ul, ur for boxes to pepper im with
    boxes = [(10, 10), (10, 70), (40, 130), (30, 200), (10, 300)]
    for x, y in boxes:
        d.rectangle((x, y, x + 50, y + 50), "black")

    #define faux template
    chos = tuple(
        b + (str(i), True, False, False) for i, b in enumerate(boxes)
    )
    tmpl, all = CONCHO((0, 0, 200, 400, "prop", "contest uno") + chos)

    #construct page, dpi only used in ratio, hence 1 vs default 0
    page = Ballot.Page(dpi=1, image=im)
    page.as_template("precinct", tmpl)

    results = ShillBallot().CapturePageInfo(page)

    assert concho_vs_vd(all, results)

    for ret in results:
        # getcolors returns None if there are more than the specifed colors
        # so we're verifying the monochromicity of the crops
        assert ret.image.getcolors(1) is not None

def IsVoted_test(): #add loop that makes a speck in the center instead of
#filling the whole thing in
    const.vote_intensity_threshold = 200
    const.dark_pixel_threshold = 741
    carve = (25, 25, 75, 75) #filled entirely
    speck = (47, 47, 53, 53) #filled barely
    def do(color, box, v, a):
        i = Image.new("RGB", (100, 100), "#fff")
        d = ImageDraw.Draw(i)
        d.rectangle((20, 20, 80, 80), fill="#000")
        d.rectangle(carve, fill="#fff")
        d.rectangle(box, fill=("#" + color*3))
        s = Ballot.IStats(i.cropstats(100, 5, 20, 20, 60, 60, 1))
        vp, ap = Ballot.IsVoted(i, s, None)
        assert vp == v and ap == a


    for v, a, colors in (
            #voted  ambig  colors
            (True,  False, "05"),
            (True,  True,  "abcde"),
            (False, False, "f"),
        ):
        for color in colors:
            do(color, carve, v, a)

    for v, a, colors in (
            #voted  ambig  colors
            (True,  False, "0"),
            (True,  True,  "5"),
            (False, False, "abcdef"),
        ):
        for color in colors:
            do(color, speck, v, a)

