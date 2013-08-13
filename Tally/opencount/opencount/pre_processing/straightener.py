import cv, math, os, time, numpy, lineDetect
import argparse

ROT_WINDOW = 2
MIN_CROP = 20
BIN_THRESHOLD = 200
BIN_COLOR = 255
ACCUMULATOR = 2.0/3.0
GRAPH = False
DEBUG = False

METHOD_MEAN = 0
METHOD_MEDIAN = 1
METHOD_TMEAN = 2

TOP = 0
BOTTOM = 1
LEFT = 2
RIGHT = 3
THRESHOLD = 1

VECTOR = ((0,-1), (0,1), (-1,0), (1,0))

def scan(img, pos, dir):
    diff = 0
    height, width = img.shape
    newPos = pos
    """
    while (diff < THRESHOLD):
        pos = newPos
        dx, dy = VECTOR[dir]
        x, y = pos
        newPos = (x+dx, y+dy)
        newX, newY = newPos
        if (newX < 0) or (newX >= width) or (newY < 0) or (newY >= height):
            # Something's wrong with the image
            break
        diff = img[newY,newX] - img[y,x]
    """
    
    while True:
        pos = newPos
        dx, dy = VECTOR[dir]
        x, y = pos
        
        if (x < 0) or (x >= width) or (y < 0) or (y >= height):
            return (0,height-1,0,width-1)[dir]
        
        if (img[y,x] > THRESHOLD):
            break
        newPos = (x+dx, y+dy)
    
    return (y,y,x,x)[dir]
    
def findBorder(img):
    height, width = img.shape
    tOff = scan(img, (int(width/2), 0), BOTTOM)
    lOff = scan(img, (0, int(height/2)), RIGHT)
    bOff = scan(img, (int(width/2), height-1), TOP)
    rOff = scan(img, (width-1, int(height/2)), LEFT)
    
    return (rOff, tOff, lOff, bOff)

def trimmedMean(arr):
    mean = numpy.mean(arr)
    if (math.isnan(mean)):
        return 0.0
    std = numpy.std(arr)
    bottomCutoff = mean - std
    topCutoff = mean + std
    if (math.isnan(mean)):
        return 0.0
    weights = [(1 if (x >= bottomCutoff and x <= topCutoff) else 0) for x in arr]
    
    return numpy.average(arr, None, weights)

'''
Crop the image by offset pixels on all sides
'''
def crop(image, hCrop, vCrop):
    hCrop += MIN_CROP
    vCrop += MIN_CROP
    hCrop = int(hCrop)
    vCrop = int(vCrop)
    cv.SetImageROI(image, (hCrop, vCrop, image.width - 2*hCrop, image.height - 2*vCrop))
    image2 = cv.CreateImage(cv.GetSize(image), image.depth, image.nChannels)
    cv.Copy(image, image2)
    
    imageMat = cv.GetMat(image2)
    return imageMat

'''
Downsize the imageMat by a factor of resizeFactor
'''
def makeThumbnail(imageMat, resizeFactor=1):
    thumbnail = cv.CreateMat(int(imageMat.rows / resizeFactor), int(imageMat.cols / resizeFactor), cv.CV_8UC1)    
    cv.Resize(imageMat, thumbnail, cv.CV_INTER_AREA)
    return thumbnail
    
'''
Convert the 8bit 1channel imageMat into an inverted binary matrix
'''
def makeBinary(imageMat):
    binThumb = cv.CreateMat(imageMat.rows, imageMat.cols, cv.CV_8UC1)
    cv.Threshold(imageMat, binThumb, BIN_THRESHOLD, BIN_COLOR, cv.CV_THRESH_BINARY_INV)
    return binThumb

def houghTransform(binaryImg, rho, theta, maxAngle, guess, method = METHOD_MEAN, graphImg = None):
    minAccumulator = int(binaryImg.width * ACCUMULATOR)
    
    binaryArray = numpy.asarray(binaryImg)
    
    lines = lineDetect.findLines(binaryArray, rho, math.radians(theta), minAccumulator, math.radians(maxAngle), math.radians(guess))

    angles = []
    
    for (rho, theta) in lines:
        if GRAPH and graphImg:
            height = graphImg.height
            
            a = math.cos(theta)
            b = math.sin(theta)
            x0 = a * rho
            y0 = b * rho
            pt1 = (cv.Round(x0 + height*(-b)), cv.Round(y0 + height*(a)))
            pt2 = (cv.Round(x0 - height*(-b)), cv.Round(y0 - height*(a)))
        
        angle = math.degrees(theta)
        
        bottomStart = min(0-guess-maxAngle, 0-guess+maxAngle)
        bottomEnd = max(0-guess-maxAngle, 0-guess+maxAngle)
        midStart = min(90-guess+maxAngle, 90-guess-maxAngle)
        midEnd = max(90-guess+maxAngle, 90-guess-maxAngle)
        topStart = min(180-guess-maxAngle, 180-guess+maxAngle)
        topEnd = max(180-guess-maxAngle, 180-guess+maxAngle)
        
        if (angle <= midEnd and angle >= midStart):
            # Probably a vertical line
            angles.append(90-angle)
        elif (angle <= bottomEnd and angle >= bottomStart):
            # Probably a horizontal line
            angles.append(-angle)
        elif (angle <= topEnd and angle >= topStart):
            # Probably a horizontal line
            angles.append(180-angle)
            
        if GRAPH and graphImg:
            cv.Line(graphImg, pt1, pt2, cv.RGB(0, 255, 0))
    
    if method == METHOD_MEAN:
        estAngle = float(numpy.mean(angles))
    elif method == METHOD_MEDIAN:
        estAngle = float(numpy.median(angles))
    else:
        estAngle = float(trimmedMean(angles))
        
    if (math.isnan(estAngle)):
        estAngle = 0.0
        
    return estAngle
        
'''
Open the image @ filename, downsize it by a factor of resizeFactor
and attempt to determine the angle of rotation by finding 
near-vertical and near-horizontal lines and averaging their angle
to the vertical or the horizontal, respectively. If GRAPH_LINES is
true, graph the detected lines on the image and save the resulting
graph in outputDir.
'''
def detectRotation(path, resizeFactor=1, maxAngle=ROT_WINDOW, outputDir="."):    
    image = cv.LoadImage(path, cv.CV_LOAD_IMAGE_GRAYSCALE)
    
    maxAngleRad = math.radians(maxAngle)
    hCrop = math.ceil(math.sin(maxAngleRad) * image.height)
    vCrop = math.ceil(math.sin(maxAngleRad) * image.width)
    imageMat = crop(image, hCrop, vCrop)
    
    thumbnail = makeThumbnail(imageMat, resizeFactor)
    binThumb = makeBinary(thumbnail)
    
    filename = os.path.split(path)[1]
    filename, ext = os.path.splitext(filename)
     
    # First pass
    
    graphImg = None
    
    if GRAPH:
        graphImg = cv.CreateMat(thumbnail.rows, thumbnail.cols, cv.CV_8UC3)
        cv.CvtColor(thumbnail, graphImg, cv.CV_GRAY2BGR)
        if DEBUG:
            print graphImg;
    
    angle1 = houghTransform(binThumb, 1, 0.1, maxAngle, 0.0, METHOD_TMEAN, graphImg)

    if GRAPH:
        cv.SaveImage(os.path.join(outputDir, 'binary_{0}{1}'.format(filename, ext)), binThumb)
        cv.SaveImage(os.path.join(outputDir, 'lines_{0}{1}'.format(filename, ext)), graphImg)
        
    # Second pass
    
    if GRAPH:
        graphImg = cv.CreateMat(thumbnail.rows, thumbnail.cols, cv.CV_8UC3)
        cv.CvtColor(thumbnail, graphImg, cv.CV_GRAY2BGR)
    
    angle2 = houghTransform(binThumb, 1, 0.01, 0.1, angle1, METHOD_MEDIAN, graphImg)
    
    if GRAPH:
        cv.SaveImage(os.path.join(outputDir, 'lines_pass2_{0}{1}'.format(filename, ext)), graphImg)

    return (angle1, angle2)

def rotateImage(image, angle):
    image_center = tuple(numpy.array(cv.GetSize(image))/2)
    rot_mat = cv.CreateMat(2, 3, cv.CV_32F)
    cv.GetRotationMatrix2D(image_center, angle, 1.0, rot_mat)
    result = cv.CreateImage(cv.GetSize(image), image.depth, image.nChannels) 
    cv.WarpAffine(image, result, rot_mat)

    return result

def fixRotation(fname, angle):
    """
    Given the path to the image, the estimated angle of rotation and an output
    directory, rotate the image by -angle and save the resulting image in
    outDir. Returns the unrotated image.
    """
    img = cv.LoadImage(fname, cv.CV_LOAD_IMAGE_COLOR)
    img = rotateImage(img, -angle)
    
    grayImg = cv.CreateMat(img.height, img.width, cv.CV_8UC1)
    cv.CvtColor(img, grayImg, cv.CV_BGR2GRAY)
    rOff, tOff, lOff, bOff = findBorder(numpy.asarray(grayImg))
    cv.SetImageROI(img, (lOff, tOff, rOff-lOff, bOff-tOff))

    #cv.SaveImage(outName, img)
    return img

def straighten_image(imgpath, outputpath, resize=2.0, maxAngle=4.0, imgsize=None):
    """
    Given an image, straighten the image (by detecting the rotation
    offset), and save the straightened image to outpath.
    If imgsize is given, then pad/crop the output image such that it
    is of size imgsize.
    Input:
        str imgpath: path to the image.
        float resize: Downsizing parameter for detectRotation.
        float maxAngle: Biggest angle to search for.
        str output: output filepath
        tuple imgsize: (width, height) in pixels
    """
    angle1, angle2 = detectRotation(imgpath, resize, maxAngle, outputpath)
    if DEBUG:
        print "Angle1: {0}, angle2: {1}".format(angle1, angle2)
    img = fixRotation(imgpath, angle2)
    if imgsize:
        w, h = imgsize
        img = size_image(img, (h,w))
    cv.SaveImage(outputpath, img)

#def size_image(img, imgsize):
#    """
#    Given an image and an image size, add padding/cropping such that
#    the return image is of size imgsize.
#    """
#    new_img = cv.CreateMat(imgsize[1], imgsize[0], cv.CV_8UC3)
#    cv.Resize(img, new_img)  # Resizes the image, bad!
#    return new_img

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

def main():
    global GRAPH, DEBUG
    
    parser = argparse.ArgumentParser(description='Straighten a rotated image.')

    parser.add_argument("-o", "--output",
                        dest="output", default="",
                        help="Output filename")
    parser.add_argument("-r", "--resize-factor",
                        dest="resize", default=2.0, type=float,
                        help="Shrinking factor")
    parser.add_argument("--size", dest="imgsize", default=None,
                        nargs=2,
                        help="Make output image be of a given size \
by padding/cropping the output image appropriately.")
    parser.add_argument("-m", "--max-angle",
                        dest="maxAngle", default=4.0, type=float,
                        help="Maximum expected angle from the vertical/horizontal (in degrees)")
    parser.add_argument("-g", "--graph", action="store_true", dest="graph",
                      default=False, help="Graph the discovered lines")
    parser.add_argument("-d", "--debug", action="store_true", dest="debug",
                      default=False, help="Print debugging info")
    parser.add_argument("input", help="Input filename")

    args = parser.parse_args()
    
    input = args.input
    output = args.output
    resize = args.resize
    maxAngle = args.maxAngle
    imgsize = args.imgsize
    GRAPH = args.graph
    DEBUG = args.debug

    startTime = time.time()
    
    if (output == ""):
        name1 = os.path.split(input)[1]
        name1, ext = os.path.splitext(input)
        output = name1 + "-unrotated" + ext
    if imgsize:
        imgsize[0] = int(imgsize[0])
        imgsize[1] = int(imgsize[1])

    straighten_image(input, output, resize=resize, maxAngle=maxAngle, imgsize=imgsize)
     
    if DEBUG:   
        print "Time Elapsed: {0}".format(time.time() - startTime)

if __name__ == "__main__":
    main()
