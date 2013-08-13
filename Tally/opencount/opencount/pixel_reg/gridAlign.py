from imagesAlign import *
from shared import *

def gridAlign(I,Iref,r,fac1=1.5,fac2=.5,vCells=3,hCells=5,verbose=False):
    ''' Description of code

    0. Roughly align image globally
    1. Perform initial alignment of the padded image region. Pad factor is fac1.
    2. Perform second alignment of the image region with gridding and a little less padding. Pad factor is fac2. Padding is necessary to manage border effects.
    3. Return patch region.
    '''

    # to account for poorly scanned borders, create nan-padded Irefs
    IrefM=maskBorders(Iref);

    # part 0
    Io=imagesAlign(I,IrefM,rszFac=.25)[1]
    
    # part 1
    fac=1.5
    (rOut,rOff)=expand(r[0],r[1],r[2],r[3],I.shape[0]-1,I.shape[1]-1,fac)
    
    I1=Io[rOut[0]:rOut[1],rOut[2]:rOut[3]]
    Iref1=Iref[rOut[0]:rOut[1],rOut[2]:rOut[3]]
    Iref1M=IrefM[rOut[0]:rOut[1],rOut[2]:rOut[3]]

    I1T=imagesAlign(I1,Iref1M)[1]

    # part 2
    fac=.1
    (rOut,rOff)=expand(rOff[0],rOff[1],rOff[2],rOff[3],I1.shape[0]-1,I1.shape[1]-1,fac)
    Iref2=Iref1[rOut[0]:rOut[1],rOut[2]:rOut[3]]
    I2=I1T[rOut[0]:rOut[1],rOut[2]:rOut[3]]

    I2T=imagesAlign(I2,Iref2,trfm_type='projective',vCells=vCells,hCells=hCells)[1]

    # part 3
    Ipt=I2T[rOff[0]:rOff[1],rOff[2]:rOff[3]]

    Irefpt=Iref[r[0]:r[1],r[2]:r[3]]
    Dabs=np.abs(Ipt-Irefpt)
    if verbose:
        Ipt0=I[r[0]:r[1],r[2]:r[3]]

        figure(0)
        imshow(Ipt0-Irefpt); title('Initial patch diff'); colorbar();
    
        figure(1)
        imshow(I1T-Iref1); title('After first round align'); colorbar();
        
        figure(2);
        imshow(Dabs); title('Final patch diff')
        colorbar();
        
        show()
    
    return (Dabs,Ipt)
