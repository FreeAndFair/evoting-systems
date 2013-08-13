from scipy import misc
from imagesAlign import *
import csv
import os
import string

# Demo of extracting targets given a template and ballot definition

bdPath=os.path.join('merced','blank_targetlocs.csv')
Iref=misc.imread(os.path.join('merced','blank.jpg'),flatten=1)/255.;
I=misc.imread(os.path.join('merced','MER01 BATCH 1-1.jpg'),flatten=1)/255.0;
bdReader=csv.reader(open(bdPath,'r'))

STACK=np.array([]); isFirst=1; pad=100

# loop over every target location
for row in bdReader:
    if isFirst:
        isFirst=0;
        continue
    x=string.atoi(row[2]); y=string.atoi(row[3]);
    w=string.atoi(row[4]); h=string.atoi(row[5]);
    I1=I[y-pad:y+h+pad,x-pad:x+w+pad]
    Iref1=Iref[y-pad:y+h+pad,x-pad:x+w+pad]
    # align locally
    IO=imagesAlign(I1,Iref1)
    targ=IO[1][pad:pad+h,pad:pad+w]
    if STACK.size == 0:
        STACK=targ;
    else:
        STACK=np.vstack([STACK,targ])

imshow(STACK,cmap='gray'); show()
