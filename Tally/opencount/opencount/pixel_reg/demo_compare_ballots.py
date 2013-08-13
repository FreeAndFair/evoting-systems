from scipy import misc
from gridAlign import *

# load images
I=misc.imread('test305.jpg',flatten=1)/255.0;
Iref=misc.imread('vbm305.jpg',flatten=1)/255.0;

# specify precinct patch region; I[i1:i2,j1:j2]
r=[140,200,60,250]; thr=.5;
t0=time.clock()
(Dabs,Ipt)=gridAlign(I,Iref,r,verbose=True)
print 'time:',time.clock()-t0,'(s)'
            
print "Sum of diffs > ", thr, " = ", np.sum(Dabs[Dabs>thr])


