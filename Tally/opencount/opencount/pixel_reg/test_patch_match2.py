import shared as sh
import os
import numpy as np
from matplotlib.pyplot import show, imshow, figure, title

# load patch
ballotDir = '../../test-ballots/1side_Ntemplates/cedar2008primary_full/blank'
I=sh.standardImread(os.path.join(ballotDir,'20120608170512502_0001.jpg'),flatten=True)

bb=[770,800,355,500]
patch = I[bb[0]:bb[1],bb[2]:bb[3]]
#imshow(patch); show()

# generate image list
imList = []
for root, dirs, files in os.walk(ballotDir):
    for f in files:
        (f0,ext)=os.path.splitext(f)
        if ext != '.jpg':
            continue
        p1=os.path.join(root,f)
        imList.append(p1)
        
#results = sh.find_patch_matches(patch,imList,region=bb)
results = sh.find_patch_matchesV1(I,bb,imList)

minOverlay=[]
maxOverlay=[]
for r1 in results:
    if len(minOverlay)==0:
        minOverlay = r1[3]
        maxOverlay = r1[3]
    else:
        tmpMat = np.zeros((r1[3].shape[0],r1[3].shape[1],2))
        tmpMat[:,:,0] = r1[3]

        tmpMat[:,:,1] = minOverlay
        minOverlay = np.min(tmpMat,axis=2)

        tmpMat[:,:,1] = maxOverlay
        maxOverlay = np.max(tmpMat,axis=2)

print 'total = ' , len(results)
figure(1);imshow(minOverlay);title('min');
figure(2);imshow(maxOverlay);title('max');
show()
