import cv, os

'''
 imgsize: (height,width) aka (rows, cols)
'''
def size_image(img, imgsize):
    # check if we need to crop out ROI
    roiWidth = img.width
    roiHeight = img.height
    if (img.width > imgsize[1]):
        roiWidth = imgsize[1]

    if (img.height > imgsize[0]):
        roiHeight = imgsize[0]
        
    roi = (0,0,roiWidth,roiHeight)
    cv.SetImageROI(img,roi)
    imgTrim=cv.CreateImage((roi[2],roi[3]),img.depth,img.nChannels)
    cv.Copy(img,imgTrim)

    # check if we need to pad
    padSize=0
    padSize=max(padSize,imgsize[0]-imgTrim.height)
    padSize=max(padSize,imgsize[1]-imgTrim.width)

    if padSize==0: # no padding needed
        return imgTrim
    else:
        padSize = int(round((padSize+.5)/2.))
        # copy make border 
        imgPad=cv.CreateImage((imgTrim.width+2*padSize,
                               imgTrim.height+2*padSize),
                              img.depth,
                              img.nChannels)
        cv.CopyMakeBorder(imgTrim,imgPad,(0,0),0)
        roi = (0,0,imgsize[1],imgsize[0])
        cv.SetImageROI(imgPad,roi)
        imgFinal=cv.CreateImage((roi[2],roi[3]),img.depth,img.nChannels)
        cv.Copy(imgPad,imgFinal)
        return imgFinal

# ========= TEST CASES BELOW ===========

def testColorSLO():
    imD = '../../test-ballots/sizetest/';
    # [2200,1700]
    Icv=cv.LoadImage(os.path.join(imD,'color.jpg'));

    # test region is same
    out=size_image(Icv,[2200,1700])
    assert(out.height==2200)
    assert(out.width==1700)

    # test region is smaller in both dims
    out=size_image(Icv,[2100,1500])
    assert(out.height==2100)
    assert(out.width==1500)
    
    # test region is larger in both dims
    out=size_image(Icv,[2400,1800])
    assert(out.height==2400)
    assert(out.width==1800)
    
    # test region is larger in both dims
    out=size_image(Icv,[2400,1500])
    assert(out.height==2400)
    assert(out.width==1500)


def testGrayLeon():
    imD = '../../test-ballots/sizetest/';
    # [2799,1708]
    Icv=cv.LoadImage(os.path.join(imD,'gray.png'));

    # test region is same
    out=size_image(Icv,[2799,1708])
    assert(out.height==2799)
    assert(out.width==1708)

    # test region is smaller in both dims
    out=size_image(Icv,[2100,1500])
    assert(out.height==2100)
    assert(out.width==1500)

    # test region is larger in both dims
    out=size_image(Icv,[2900,1800])
    assert(out.height==2900)
    assert(out.width==1800)
    
    # test region is larger in one dim
    out=size_image(Icv,[2400,1708])
    assert(out.height==2400)
    assert(out.width==1708)

def testGrayLeon():
    imD = '../../test-ballots/sizetest/';
    # [2799,1708]
    Icv=cv.LoadImage(os.path.join(imD,'gray.png'));

    # test region is same
    out=size_image(Icv,[2799,1708])
    assert(out.height==2799)
    assert(out.width==1708)

    # test region is smaller in both dims
    out=size_image(Icv,[2100,1500])
    assert(out.height==2100)
    assert(out.width==1500)

    # test region is larger in both dims
    out=size_image(Icv,[2900,1800])
    assert(out.height==2900)
    assert(out.width==1800)
    
    # test region is larger in one dim
    out=size_image(Icv,[2400,1708])
    assert(out.height==2400)
    assert(out.width==1708)

def testMono():
    imD = '../../test-ballots/sizetest/';
    # [2200,1704]
    Icv=cv.LoadImage(os.path.join(imD,'mono.tif'));

    # test region is same
    out=size_image(Icv,[2200,1704])
    assert(out.height==2200)
    assert(out.width==1704)

    # test region is smaller in both dims
    out=size_image(Icv,[2000,1500])
    assert(out.height==2000)
    assert(out.width==1500)

    # test region is larger in both dims
    out=size_image(Icv,[2900,1800])
    assert(out.height==2900)
    assert(out.width==1800)
    
    # test region is larger in one dim
    out=size_image(Icv,[2000,1708])
    assert(out.height==2000)
    assert(out.width==1708)

testMono()
testGrayLeon()
testColorSLO()
