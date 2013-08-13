import imagesAlign as lk
import shared as sh
import os
import numpy as np
from matplotlib.pyplot import show, imshow, figure, title

# load patch
img_dir = '../../test-ballots/carlini/'

Iref=sh.standardImread(os.path.join(img_dir,'0.tif'),flatten=True)
M = np.zeros((Iref.shape[0],Iref.shape[1], 11))

for i in range(11):
    I=sh.standardImread(os.path.join(img_dir,str(i+1)+'.tif'),flatten=True)
    Inorm = np.zeros(Iref.shape)
    # make patch the same size as Iref

    min0 = min(I.shape[0],Iref.shape[0])
    min1 = min(I.shape[1],Iref.shape[1])
    Inorm[0:min0,0:min1] = I[0:min0,0:min1]

    diff0 = Iref.shape[0] - I.shape[0]
    diff1 = Iref.shape[1] - I.shape[1]

    if diff0 > 0:
        Inorm[I.shape[0]:I.shape[0]+diff0,:] = 1
    if diff1 > 0:
        Inorm[:,I.shape[1]:I.shape[1]+diff1] = 1

    res=lk.imagesAlign(Inorm,Iref)
    M[:,:,i] = res[1]

meanOverlay = np.mean(M,axis=2)
minOverlay = np.min(M,axis=2)
maxOverlay = np.min(M,axis=2)
figure(0); imshow(meanOverlay,cmap='gray'); title('mean')
figure(1); imshow(minOverlay,cmap='gray'); title('min')
figure(2); imshow(maxOverlay,cmap='gray'); title('max')
show()
