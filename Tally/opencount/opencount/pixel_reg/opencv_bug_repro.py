import pdb
import cv
import numpy as np
from matplotlib.pyplot import show, imshow, figure

I=np.round(np.load('debug_I.npy')*255.)/255.
patch=np.round(np.load('debug_patch.npy')*255.)/255.

#Ifoo=np.float32(misc.imread('debug_I.png')/255.0)
#patchfoo=np.float32(misc.imread('debug_patch.png')/255.0)

patchCv=cv.fromarray(np.copy(patch))
ICv=cv.fromarray(np.copy(I))
# call template match
outCv=cv.CreateMat(I.shape[0]-patch.shape[0]+1,I.shape[1]-patch.shape[1]+1,patchCv.type)
cv.MatchTemplate(ICv,patchCv,outCv,cv.CV_TM_CCOEFF_NORMED)
Iout=np.asarray(outCv)
YX=np.unravel_index(Iout.argmax(),Iout.shape)

#misc.imsave('debug_I.png',I)
#misc.imsave('debug_patch.png',patch)

pdb.set_trace()
figure(1); imshow(I);
figure(2); imshow(patch);
figure(3); imshow(Iout);
show()

