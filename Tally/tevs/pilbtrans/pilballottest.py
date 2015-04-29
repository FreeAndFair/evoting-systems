import pilballot
import sys
import Image

bytes_per_pixel = 1
if len(sys.argv) < 4:
    print "usage: pilballottest infilename outfilename mode"
    print "       mode from L (luminance) or RGB or RGBA"
    print
    print "Reports pixel counts of low intensity, high intensity pixels"
    print "from image in infilename, writes version to outfilename with"
    print "pixel minimum intensity raised to 128."
    sys.exit(-1)
im = Image.open(sys.argv[1])
im.load()
imIn = im
imIn.load()
print imIn.mode
imIn = im.convert(sys.argv[3])
imOut = Image.new(imIn.mode,imIn.size,None)
if imIn.mode == "RGBA" or imIn.mode == "RGB":
    bytes_per_pixel = 4
print "Bytes per pixel:",bytes_per_pixel
pilballot.bias(imIn.im.id, imOut.im.id, bytes_per_pixel)
print "(Lo,Hi)",pilballot.stats(imIn.im.id, bytes_per_pixel)
imOut.save(sys.argv[2])
print "Wrote",sys.argv[2]
