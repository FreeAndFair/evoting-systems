from PIL import Image

#thresholds for colors
lowest_bin = 64
low_bin = 128
high_bin = 192

def cropstats(im, x, y):
    data = im.load()
    columns = im.size[0]
    rows = im.size[1]
    tot = [0, 0, 0]
    avg = [0., 0., 0.]
    lowest = [0, 0, 0]
    low = [0, 0, 0]
    high = [0, 0, 0]
    highest = [0, 0, 0]
    interior_dark = 0

    rl = rows/4
    rh = (3*rows)/4
    cl = columns/4
    ch = (3*columns)/4
    for r in range(rows):
        for c in range(columns):
            datum = data[c, r]
            for color in range(3):
                dc = datum[color]
                tot[color] += dc
                if all((dc < low_bin, r > rl, r < rh, c > cl, c < ch)):
                    interior_dark += 1
                if dc < lowest_bin:
                    lowest[color] += 1
                elif dc < low_bin:
                    low[color] += 1
                elif dc < high_bin:
                    high[color] += 1
                else: #highest_bin
                    highest[color] +=1

    rc = float(rows * columns)

    # return the information, for now, as cropstats in PILB;
    # later, put in Istats form
    retlist = []
    for color in range(3):
        retlist.append(tot[color] / rc)
        retlist.append(lowest[color])
        retlist.append(low[color])
        retlist.append(high[color])
        retlist.append(highest[color])
    retlist.append(x)
    retlist.append(y)
    retlist.append(interior_dark)

    return retlist

if __name__ == "__main__":
    try:
        filename = sys.argv[1]
        im = Image.open(filename)
        print "Testing on image of size (%d, %d)." % im.size
        print cropstats(im, 0, 0)
    except IndexError:
        print >>sys.stderr, "usage: python cropstats2.py image_filename"
        sys.exit(2)
    except IOError:
        print "could not open", filename
        sys.exit(1)
