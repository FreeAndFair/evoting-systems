import sys, os, site
site.addsitedir('/home/jimmy/tevs')
from PILB import Image
im = Image.open("test.jpg")
print im.samplefunc(300,0)
