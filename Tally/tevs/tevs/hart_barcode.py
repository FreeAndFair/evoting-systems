# hart_barcode.py
import Image, ImageStat
import pdb
import sys
import logging

class BarcodeException(Exception):
    "Raised if barcode not properly interpreted"
    pass

def hart_barcode(image,x,y,w,h):
    """read a vertical barcode on a hart ballot, as in getbarcode in PILB"""
    whites_list = []
    blacks_list = []
    whitethresh = 128
    croplist = (x,y,x+w,y+h)
    crop = image.crop(croplist)
    # 1) scan down all lines, deciding white or black
    firsttime = True
    lastwhite = True
    whitecount = 0
    blackcount = 0
    for y in range(crop.size[1]-1,0,-1):
        linecroplist = (0,y,crop.size[0],y+1)
        linecrop = crop.crop(linecroplist)
        linemean = ImageStat.Stat(linecrop).mean[0]
        if linemean > whitethresh:
            if lastwhite:
                whitecount += 1
            else:
                blacks_list.append(blackcount)
                blackcount = 0
                whitecount = 1
                lastwhite = True
        else:
            if not lastwhite:
                blackcount += 1
            else:
                if firsttime: firsttime = False
                else:
                    whites_list.append(whitecount)
                    whitecount = 0
                    blackcount = 1
                    lastwhite = False
    # 2) determine average length of blacks, whites;
    # replace original lengths with True for narrow, False for wide
    bsum = 0
    avg = 0
    for b in blacks_list:
        bsum += b
    try:
        avg = bsum/len(blacks_list)
    except ZeroDivisionError:
        raise BarcodeException("No black stripes found in barcode region.")

    # convert wide -->True, narrow-->False
    blacks_list = map(lambda el: el >= avg, blacks_list)    
    wsum = 0
    avg = 0
    whites_list = whites_list[1:]
    for w in whites_list:
        wsum += w
    try:
        avg = wsum/len(whites_list)
    except ZeroDivisionError:
        raise BarcodeException("No white stripes found in barcode region.")
    # after trimming initial white (not part of bar code)
    # first two whites, first two blacks must be narrow 
    # convert wide -->True, narrow-->False
    whites_list = map(lambda el: el >= avg, whites_list)
    # first two whites, first two blacks should be narrow (False)
    if (blacks_list[0] 
            or blacks_list[1] 
            or whites_list[0] 
            or whites_list[1]):
        logging.getLogger('').debug("Problem with bar code: not finding start group.")
    # process seven groups of five blacks, five whites
    # expect exactly two wides
    values = [0,0,0,0,0,0,0, 0,0,0,0,0,0,0]
    try:
        for group in range(7):
            bvalue = 0
            wvalue = 0
            if blacks_list[2+(group*5)+0]:
                bvalue += 1
            if blacks_list[2+(group*5)+1]:
                bvalue += 2
            if blacks_list[2+(group*5)+2]:
                bvalue += 4
            if blacks_list[2+(group*5)+3]:
                bvalue += 7
            if bvalue == 11: bvalue = 0

            if whites_list[2+(group*5)+0]:
                wvalue += 1
            if whites_list[2+(group*5)+1]:
                wvalue += 2
            if whites_list[2+(group*5)+2]:
                wvalue += 4
            if whites_list[2+(group*5)+3]:
                wvalue += 7
            if wvalue == 11: wvalue = 0
            values[group*2] = bvalue
            values[1+(group*2)] = wvalue
    
        retval = "%d%d%d%d%d%d%d%d%d%d%d%d%d%d" % (
            values[0],values[1],values[2],values[3],
            values[4],values[5],values[6],values[7],
            values[8],values[9],values[10],values[11],values[12],values[13]
            )
    except IndexError:
        retval = "FLIP?"
    return (retval)

if __name__ == "__main__":
    if len(sys.argv)<6:
        print "usage: python hartbarcode.py image x y w h"
        sys.exit(1)
    image = Image.open(sys.argv[1])
    x,y,w,h = int(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4]),int(sys.argv[5])
    print x,y,w,h
    try:
        barcode = hart_barcode(image,x,y,w,h)
    except BarcodeException as e:
        print e
        barcode = "NOBARCODE"
        pdb.set_trace()
    print "Barcode",barcode
    if barcode == "FLIP?":
        barcode = hart_barcode(image.rotate(180),x,y,w,h)
        print "Barcode of flip",barcode
    sys.exit(0)
