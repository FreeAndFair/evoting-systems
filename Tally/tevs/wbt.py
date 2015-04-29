# open image given as sys.argv[1]
# find landmarks and rotate (TBD)
# take boxes of dimensions/sys.argv[2] sys.argv[2]-->screen size 
# e.g. 1/100 of height and 1/100 of width
# report number of transitions white to black for each column
# extend to report per 10th of height, to find partial columns
# divide image into columns based on peaks of reported transitions,
# rotate each column 90 degrees and repeat to find lines/blocks of text
import sys
import Image
import ImageStat
import ImageDraw
import os
import pdb

print "==>", sys.argv[1]

im = Image.open(sys.argv[1]).convert("RGB")
scratch = ImageDraw.Draw(im )
screen = int(sys.argv[2])

xinc = im.size[0]/screen + 1
yinc = im.size[1]/screen + 1
print "(x+,y+)=", xinc, yinc

def getMedian(numericValues):
  theValues = sorted(numericValues.values())
  if len(theValues) % 2 == 1:
      return theValues[(len(theValues)+1)/2 - 1]
  else:
      lower = theValues[len(theValues)/2 - 1]
      upper = theValues[len(theValues)/2]
      return int(round((float(lower + upper)) / 2))  

def mode(vals):
    freqs = {}
    for val in vals:
        freqs[val] = freqs.get(val, 0)+1
    return freqs[max(freqs.keys())]

def pstats(title, stat, transition):
    print "%s = %d" % (title, stat) 
    counter = 0
    for n in range(screen):
        m = transition.get(n, 0)
        if m > stat:
            print "%d: %d" % (n*xinc, m),
            counter += 1
            if counter % 5 == 0:
                print
    print "\n%d out of %d\n" % (counter, len(transition))


hmap, vmap = {}, {}
def hit(x, y):
    if x not in hmap:
        hmap[x] = [y]
    else:
        hmap[x].append(y)
    if y not in vmap:
        vmap[y] = [x]
    else:
        vmap[y].append(x)

thresh = 128

def run(im, xinc, yinc):
    transition, transitionat = {}, []
    for y in range(yinc, im.size[1] - yinc, yinc):
        islight = True
        for x in range(xinc, im.size[0] - xinc, xinc):
            cs = ImageStat.Stat(im.crop((x, y, x+xinc, y+yinc)))
            darkestred = cs.extrema[0][0]#round(int( sum(x for x, _ in cs.extrema) / 3.0))
            if not islight and darkestred > thresh:
                islight = True
            if islight and darkestred <= thresh:
                islight = False
                transition[x/xinc] = transition.get(x/xinc, 0) + 1
                transitionat.append((x,y))
                hit(x, y)
    return transition, transitionat

def runv(im, xinc, yinc):
    transition, transitionat = {}, []
    for x in range(xinc, im.size[0] - xinc, xinc):
        islight = True
        for y in range(yinc, im.size[1] - yinc, yinc):
            cs = ImageStat.Stat(im.crop((x, y, x+xinc, y+yinc)))
            dred = cs.extrema[0][0]#round(int( sum(x for x, _ in cs.extrema) / 3.0))
            if not islight and dred > thresh:
                islight = True
            if islight and dred <= thresh:
                islight = False
                transition[y/yinc] = transition.get(y/yinc, 0) + 1
                transitionat.append((x, y))
                hit(x, y)
    return transition, transitionat



def hmap_ln():  
    pot_lns = []
    for x, ys in hmap.iteritems():
        last_y = -1
        pot_st = None
        c = 0
        for y in sorted(ys):
            if y == last_y + yinc:
                if pot_st is None:
                    pot_st = (x, y)
                c = 0
                c += 1
            elif pot_st is not None:
                if c > 4:
                    pot_lns.append(pot_st + (x, y))
                pot_st = None
            last_y = y
        if pot_st is not None and c > 4: #don't lose line if we fell off edge of ys
            pot_lns.append(pot_st + (x, last_y))
        return pot_lns

def vmap_ln():
    pot_lns = []
    for y, xs in vmap.iteritems():
        last_x = -1
        pot_st = None
        c = 0
        for x in sorted(xs):
            if x == last_x + xinc:
                if pot_st is None:
                    pot_st = (x, y)
                    c = 0
                c += 1
            elif pot_st is not None:
                if c > 4:
                    pot_lns.append(pot_st + (x, y))
                pot_st = None
            last_x = x
    if pot_st is not None and c > 4:
        pot_lns.append(pot_st + (last_x, y))
    return pot_lns


def get_bighist():
    big_hist = {}
    for x, ys in hmap.iteritems():
        big_hist[x] = len(ys)
    return big_hist

slc_count = 10
slices = im.size[1]/slc_count
def get_lilhists(): #[bin no]{xs:yc}
    lil_hists = []
    for _ in range(slc_count): #make bins
        lil_hists.append({})
    for x, ys in hmap.iteritems():
        for y in sorted(ys):
            bn = y / slices
            lil_hists[bn][x] = lil_hists[bn].get(x, 0) + 1
    return lil_hists


def draw_tat_mark(tat):
    for t in tat:
        scratch.rectangle(
            (t[0], t[1], t[0]+xinc, t[1]+2),
            fill="#00f")

def draw_potlns():
    for a, b, c, d in pot_lns:
        scratch.rectangle((a, b, c+2, d+2), fill="#f00")

def draw_bighist():
    for x, yc in get_bighist().iteritems():
        scratch.rectangle((x, im.size[1]-yc*xinc, x+xinc-2, im.size[1]), fill="#0f0")

def draw_lilhists(lh):
    for n, sec in enumerate(lh): #slice number and local histogram
        for x, yc in sec.iteritems():
            scratch.rectangle((x, (n+1)*slices - yc*xinc, x+xinc-2, (n+1)*slices),
                fill="#0f0")



#COMPUTE
t1, tat1 = run(im, xinc, yinc)
#t2, tat2 = runv(im, xinc, yinc)

pot_lns = hmap_ln()
pot_lns.extend(vmap_ln())


#DRAW 
draw_tat_mark(tat1)
#draw_tat_mark(tat2)
draw_lilhists(get_lilhists())





im.save("outimages/" + os.path.basename(sys.argv[1]))


median = getMedian(t1)
average = sum(t1)/(screen + 1)

#pstats("Median",            median,     t1)
#pstats("Twice median",      2*median,   t1)
#pstats("Arithmetic mean",   average,    t1)
#pstats("Twice a. mean",     2*average,  t1)


# and note w->b transitions of each row
# build x-array of transition counts, note largest counts
# attempt to detect repeating pattern of transitions
