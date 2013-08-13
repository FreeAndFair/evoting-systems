from scipy import misc,ndimage
from shared import *
from imagesAlign import *
import csv
import os
import string
import sys

def maskImage(I,csvFile):
    ''' Set regions arounds targets to be NANs '''
    Iout=np.copy(I);
    bdReader=csv.reader(open(csvFile,'r'))
    isFirst=True; pFac=.1;
    # loop over every target location
    for row in bdReader:
        if isFirst:
            isFirst=False;
            continue
        isContest=string.atoi(row[7]);
        if isContest==1:
            continue
        x1=string.atoi(row[2]); x2=x1+string.atoi(row[4]);
        y1=string.atoi(row[3]); y2=y1+string.atoi(row[5]);
        # expand region around target
        (rOut,rOff)=expand(y1,y2,x1,x2,I.shape[0],Iout.shape[1],pFac)
        Iout[rOut[0]:rOut[1],rOut[2]:rOut[3]]=np.nan;
    return Iout;


def extractTargets(I,Iref,csvFile):
    ''' Perform local alignment around each target, then crop out target  '''
    bdReader=csv.reader(open(csvFile,'r'))

    IrefM=maskImage(Iref,csvFile);

    result = []

    isFirst=True; pFac=2;
    # loop over every target location
    for row in bdReader:
        if isFirst:
            isFirst=False;
            continue
        isContest=string.atoi(row[7]);
        if isContest==1:
            continue
        x1=string.atoi(row[2]); x2=x1+string.atoi(row[4]);
        y1=string.atoi(row[3]); y2=y1+string.atoi(row[5]);
        # expand region around target
        (rOut,rOff)=expand(y1,y2,x1,x2,I.shape[0],I.shape[1],pFac)
        I1=I[rOut[0]:rOut[1],rOut[2]:rOut[3]];
        Iref1=IrefM[rOut[0]:rOut[1],rOut[2]:rOut[3]];        

        IO=imagesAlign(I1,Iref1)
        targ=IO[1][rOff[0]:rOff[1],rOff[2]:rOff[3]];
        result.append(targ)
            
    return result

def convertImages(csvP, IrefP, ballotD):
    Iref=misc.imread(IrefP,flatten=1)/255.;
    
    for root,dirs,files in os.walk(ballotD):
        for f1 in files:
            if not(f1.endswith('jpg')):
                continue
            
            # 1. check if ballot is flipped
            I=misc.imread(os.path.join(root,f1),flatten=1)/255.0;
    
            rszFac=.25
            # rotate image
            IR=ndimage.interpolation.rotate(I,180)
            (H,Io,err)=imagesAlign(I,Iref,rszFac=rszFac,verbose=False)
            (HR,IoR,errR)=imagesAlign(IR,Iref,rszFac=rszFac,verbose=False)
    
            if err>errR:
                #print f1,' is rotated. diff = ', np.abs(err-errR);
                Iin=IR
            else:
                #print f1,' is NOT rotated. diff = ', np.abs(err-errR);
                Iin=I
    
            #imshow(STACK,cmap='gray');
            #savefig(os.path.join(root,f1+'.pdf'))
            return extractTargets(Iin,Iref,csvP)
    


if __name__ == "__main__":
    if len(sys.argv) != 4:
        print 'Bad input. Example: python pressGo.py targets.csv blank.jpg ballotD'
        sys.exit()
    
    csvP=sys.argv[1]
    IrefP=sys.argv[2]
    ballotD=sys.argv[3]
    Iref=misc.imread(IrefP,flatten=1)/255.;
    
    for root,dirs,files in os.walk(ballotD):
        for f1 in files:
            if not(f1.endswith('jpg')):
                continue
            
            # 1. check if ballot is flipped
            I=misc.imread(os.path.join(root,f1),flatten=1)/255.0;
    
            rszFac=.25
            # rotate image
            IR=ndimage.interpolation.rotate(I,180)
            (H,Io,err)=imagesAlign(I,Iref,rszFac=rszFac,verbose=False)
            (HR,IoR,errR)=imagesAlign(IR,Iref,rszFac=rszFac,verbose=False)
    
            if err>errR:
                print f1,' is rotated. diff = ', np.abs(err-errR);
                Iin=IR
            else:
                print f1,' is NOT rotated. diff = ', np.abs(err-errR);
                Iin=I
    
            STACK=extractTargets(Iin,Iref,csvP)
            imshow(STACK,cmap='gray');
            savefig(os.path.join(root,f1+'.pdf'))
    
