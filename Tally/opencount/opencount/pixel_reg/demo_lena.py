import cProfile
import cv2
from scipy import misc
from shared import standardImread
from imagesAlign import imagesAlign, pttransform
import pdb
import numpy as np
import matplotlib.pyplot as plt

import pstats

# convert to double
I=standardImread('lena_t.png')
Iref=standardImread('lena.png')

IO=imagesAlign(I,Iref)
#p = pstats.Stats('profile_imagesalign1')
#p.strip_dirs().sort_stats('cumulative').print_stats(25)

viz=True
if viz:
    H=IO[0]
    # figure(0)
    # imshow(np.abs(Iref-I),cmap='gray');

    plt.figure(1)
    plt.imshow(np.abs(Iref-IO[1]),cmap='gray');

    pt0=np.array([155,65,1])
    plt.figure(2)
    plt.imshow(I,cmap='gray');
    plt.annotate('x',[pt0[0],pt0[1]])

    plt.figure(3)
    plt.imshow(IO[1],cmap='gray');
    plt.annotate('x',[pt0[0],pt0[1]])

    plt.figure(4)
    plt.imshow(I,cmap='gray');

    pt1=pttransform(I,np.linalg.inv(H),pt0);
    plt.annotate('x',[pt1[0],pt1[1]])

    plt.show();
