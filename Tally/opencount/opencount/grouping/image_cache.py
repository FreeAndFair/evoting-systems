import sys, os, time, pdb, traceback
from collections import deque
import Image, cv, scipy.misc, numpy as np

"""
A module to help maintain an in-memory cache of images. 

Designed to prevent memory usage from spiraling madly out of control.

WARNING: PIL has an upper-limit on how many files can be open at once!
         For this reason, DO NOT USE THE PIL mode!

TODO
- estimate_imgsize_bytes for OpenCV is always an overestimate, but I
  don't know why. 
"""

SIZECAP_UNBOUNDED = -1

IM_FORMAT_PIL = 0
IM_FORMAT_SCIPY = 1
IM_FORMAT_OPENCV = 2
IM_FORMAT_BINARYDATA = 3

IM_MODE_GRAYSCALE = 3
IM_MODE_RGB = 4
IM_MODE_UNCHANGED = 5

DEBUG = False

def _load_pil(imgpath, img_mode=IM_MODE_UNCHANGED):
    img = Image.open(imgpath)

    if img_mode == IM_MODE_GRAYSCALE:
        if img.mode != "L":
            img = img.convert("L")
    elif img_mode == IM_MODE_RGB:
        if img.mode != "RGB":
            img = img.convert("RGB")

    return img

def _load_scipy(imgpath, img_mode=IM_MODE_UNCHANGED):
    if img_mode == IM_MODE_GRAYSCALE:
        return scipy.misc.imread(imgpath, flatten=True)
    elif img_mode == IM_MODE_RGB:
        img = scipy.misc.imread(imgpath)
        if len(img.shape) != 3:
            newimg = np.zeros((img.shape[0], img.shape[1], 3), dtype=img.dtype)
            newimg[:,:,0] = img
            newimg[:,:,1] = img
            newimg[:,:,2] = img
            return newimg
        return img
    else:
        return scipy.misc.imread(imgpath)

def _load_opencv(imgpath, img_mode=IM_MODE_UNCHANGED):
    if img_mode == IM_MODE_GRAYSCALE:
        return cv.LoadImage(imgpath, cv.CV_LOAD_IMAGE_GRAYSCALE)
    elif img_mode == IM_MODE_RGB:
        return cv.LoadImage(imgpath, cv.CV_LOAD_IMAGE_COLOR)
    else:
        return cv.LoadImage(imgpath, cv.CV_LOAD_IMAGE_UNCHANGED)

def _load_binarydata(idx, fimgdata, imgdims, img_mode=IM_MODE_GRAYSCALE):
    """ Loads in image data from an input binary file.
    Input:
        int IDX: 
        file FIMGDATA:
        tuple IMGDIMS: (int w, int h)
    Output:
        nparray img.
    """
    w, h = imgdims
    step = w * h
    i0 = idx * step
    fimgdata.seek(i0)
    dat = np.fromstring(fimgdata.read(step), dtype='uint8')
    return dat.reshape((h, w))

_imgload_fns = {IM_FORMAT_PIL: _load_pil,
                IM_FORMAT_SCIPY: _load_scipy,
                IM_FORMAT_OPENCV: _load_opencv,
                IM_FORMAT_BINARYDATA: _load_binarydata}

class ImageCache(object):
    
    def __init__(self, SIZECAP=SIZECAP_UNBOUNDED, img_format=IM_FORMAT_SCIPY, img_mode=IM_MODE_UNCHANGED):
        """
        Input:
            int SIZECAP: 
                An integer specifying how many Megabytes (MB) that the
                ImageCache can take up at most. 
                If SIZECAP is SIZECAP_UNBOUNDED, then there is no bound.
                However, be aware that you may run out of memory if you
                load too many images!
            int IMG_FORMAT:
                Specifes which output format (PIL, scipy, OpenCV) the
                images should be returned as.
            int IMG_MODE:
                Specifies if you want the images in Grayscale or RGB
                format. If you want the original image (i.e. without
                doing any grayscale/rgb conversions), pass in IM_MODE_UNCHANGED.
        """
        if SIZECAP == SIZECAP_UNBOUNDED:
            self.sizecap = SIZECAP_UNBOUNDED
        else:
            self.sizecap = SIZECAP * 1e6

        # dict self.ID2DATA: maps {int ID: (data IMG, str IMGPATH)}
        self.id2data = {}
        self.img_format = img_format
        self.img_mode = img_mode

        self.imgpath2id = {} # maps {str imgpath: int id}
        self.ids = deque() # [int id_0, ...]

        # dict BINARYDATS_MAP: {str dataP: (file DATAFILE, tuple IMGDIMS)
        self.binarydats_map = {}

        self._curid = 0

        self.cache_imgSizes = {} # maps {int id: int size}
        self._size = 0

        self._imgload_fn = _imgload_fns[self.img_format]

    def load(self, imgpath):
        """ Loads the img pointed to by IMGPATH. Handles all the cache
        hit/miss details.
        Input:
            str IMGPATH
        Output:
            ((obj IMG, str IMGPATH),  bool isHit)
        """
        return self.cache_retrieve(imgpath)

    def load_binarydat(self, idx, dataP):
        """ Loads image from binary file DATAP, at index IDX. DataP must
        have been registered with ImageCache.register_binarydat.
        Input:
            int IDX:
            str DATAP:
        Output:
            ((obj IMG, int IDX), bool isHit)
        """
        if dataP not in self.binarydats_map:
            print "(ImageCache) Binary datafile '{0}' was not registered. Try \
first calling ImageCache.register_binarydat.".format(dataP)
            return None
        return self.cache_retrieve(idx, dataP=dataP)

    def register_binarydat(self, dataP, imgdims):
        """ Registers a binary image file with this ImageCache. The binary
        file must contain grayscale images of the same size, in byte format
        (0-255).
        Input:
            str DATAP:
            tuple IMGDIMS: (int w, int h)
        Output:
            True if registered successfully, False o.w.
        """
        try:
            f = open(dataP, 'rb')
        except IOError as e:
            print "(ImageCache) Couldn't open binary data file:", dataP
            return False

        self.binarydats_map[dataP] = (f, imgdims)
        return True

    def cache_retrieve(self, imgpath, dataP=None):
        """ If IMGPATH is already in the cache, return it.
        Else, read it from disk, and evict another image if necessary.
        If DATAP is given, and is in self.binarydats_map, then IMGPATH
        refers to an integer index within the binary image datafile at
        DATAP.
        Input:
            str IMGPATH
            str DATAP:
        Output:
            ((obj IMG, str IMGPATH), bool isHit)
        """
        if dataP != None:
            imgID = self.imgpath2id.get((imgpath, dataP), None)
        else:
            imgID = self.imgpath2id.get(imgpath, None)
        if imgID != None:
            print_dbg("== Cache Hit!")
            return (self.id2data[imgID], True)
        else:
            print_dbg("== Cache Miss!")
            imgID = self._curid
            self._curid += 1

            if dataP != None:
                self.imgpath2id[(imgpath, dataP)] = imgID
            else:
                self.imgpath2id[imgpath] = imgID
            self.ids.appendleft(imgID)
            if dataP != None:
                fdata, imgdims = self.binarydats_map[dataP]
                img = _load_binarydata(imgpath, fdata, imgdims)
            else:
                img = self._imgload_fn(imgpath, img_mode=self.img_mode)
            
            if dataP != None:
                self.id2data[imgID] = (img, (imgpath, dataP))
            else:
                self.id2data[imgID] = (img, imgpath)

            self.register_imgsize(img, imgID)
            self.cache_evict()
            if dataP != None:
                return (img, (imgpath, dataP)), False
            else:
                return ((img, imgpath), False)
            
    def cache_evict(self):
        """ If the Cache is full, remove images until it's not full. 
        Returns the number of images removed. 
        """
        if self.sizecap == SIZECAP_UNBOUNDED:
            return 0
        cur_size = self.cache_computeSize()
        num_evicted = 0
        while cur_size > self.sizecap:
            id_evictee = self.ids.pop()
            print_dbg("== CacheEvict ({0} MB / {1} MB): {2}".format(cur_size / 1e6, self.sizecap / 1e6, id_evictee))
            _, imgpath = self.id2data.pop(id_evictee)
            self.imgpath2id.pop(imgpath)
            size_evictee = self.cache_imgSizes.pop(id_evictee)
            cur_size -= size_evictee
            num_evicted += 1
        self._size = cur_size
        return num_evicted

    def cache_isFull(self):
        if self.sizecap == SIZECAP_UNBOUNDED:
            return False
        return self.cache_computeSize() < self.sizecap

    def cache_computeSize(self):
        if self._size != None:
            return self._size
        self._size = 0
        for imgID, size_bytes in self.cache_imgSizes.iteritems():
            self._size += size_bytes
        return self._size
        
    def register_imgsize(self, img, imgID):
        imgsize_bytes = estimate_imgsize_bytes(img, self.img_format)
        self.cache_imgSizes[imgID] = imgsize_bytes
        self._size += imgsize_bytes
        
def estimate_imgsize_bytes(img, img_format):
    """ Given an image IMG with format IMG_FORMAT (PIL, scipy, OpenCV),
    estimate how much space it consumes in-memory. 
    """
    # (over)-estimate size of each pixel value to be Float32.
    SIZE_PIX_BYTES = 32

    if img_format == IM_FORMAT_PIL:
        size = img.size[0] * img.size[1] * SIZE_PIX_BYTES
        if img.mode == 'RGB':
            size *= 3
        elif img.mode == 'RGBA':
            size *= 4
    elif img_format in (IM_FORMAT_SCIPY, IM_FORMAT_BINARYDATA):
        size = img.nbytes
    else:
        w, h = cv.GetSize(img)
        channels = img.nChannels
        pix_byte = SIZE_PIX_BYTES
        if img.depth in (cv.IPL_DEPTH_8U, cv.IPL_DEPTH_8S):
            pix_byte = 8
        elif img.depth in (cv.IPL_DEPTH_16U, cv.IPL_DEPTH_16S):
            pix_byte = 16
        elif img.depth in (cv.IPL_DEPTH_32F, cv.IPL_DEPTH_32S):
            pix_byte = 32
        elif img.depth in (cv.IPL_DEPTH_64F,):
            pix_byte = 64
        # Divide by 6 because...I have no idea. Too large of an
        # estimate otherwise. Wat.
        size = (w * h * channels * pix_byte / 6)
    return size

def print_dbg(*args):
    if DEBUG:
        for arg in args:
            print arg,
        print

def test_unbounded(imgsdir, imgsdir2):
    """ A simple set of tests to sanity check cache behavior for UNBOUNDED
    cache sizes.
    """
    img_cache = ImageCache(SIZECAP=SIZECAP_UNBOUNDED,
                           img_format=IM_FORMAT_SCIPY,
                           img_mode=IM_MODE_GRAYSCALE)

    t = time.time()
    img_cnt = 0
    for dirpath, dirnames, filenames in os.walk(imgsdir):
        for imgname in [f for f in filenames if f.lower().endswith('.png')]:
            imgpath = os.path.join(dirpath, imgname)
            (img, _imgpath), isHit = img_cache.load(imgpath)
            if imgpath != _imgpath:
                print "imgpaths not equal!"
                pdb.set_trace()
            if isHit != False:
                print "WHAT"
                pdb.set_trace()
            img_cnt += 1
    dur_loadImages = time.time() - t

    print "Done loading in images ({0:.6f}s).".format(dur_loadImages)

    t = time.time()
    for dirpath, dirnames, filenames in os.walk(imgsdir):
        for imgname in [f for f in filenames if f.lower().endswith('.png')]:
            imgpath = os.path.join(dirpath, imgname)
            (img, _imgpath), isHit = img_cache.load(imgpath)
            if imgpath != _imgpath:
                print "imgpaths not equal!"
                pdb.set_trace()
            if isHit != True:
                print "WHAT"
                pdb.set_trace()
    dur_readImages = time.time() - t

    t = time.time()
    for dirpath, dirnames, filenames in os.walk(imgsdir2):
        for imgname in [f for f in filenames if f.lower().endswith(".png")]:
            imgpath = os.path.join(dirpath, imgname)
            (img, _imgpath), isHit = img_cache.load(imgpath)
            if imgpath != _imgpath:
                print "imgpaths not equal!"
                pdb.set_trace()
            if isHit != False:
                print "WHAT"
                pdb.set_trace()
    dur_readImages2 = time.time() - t

    t = time.time()
    for dirpath, dirnames, filenames in os.walk(imgsdir2):
        for imgname in [f for f in filenames if f.lower().endswith(".png")]:
            imgpath = os.path.join(dirpath, imgname)
            (img, _imgpath), isHit = img_cache.load(imgpath)
            if imgpath != _imgpath:
                print "imgpaths not equal!"
                pdb.set_trace()
            if isHit != True:
                print "WHAT"
                pdb.set_trace()
    dur_readImages3 = time.time() - t

    print "==== Done ===="

    print "Loading in images ({0:.6f}s).".format(dur_loadImages)
    print "    Avg.Time: {0:.8f}s".format(dur_loadImages / float(img_cnt))
    print "Reading in images ({0:.6f}s).".format(dur_readImages)
    print "    Avg.Time: {0:.8f}s".format(dur_readImages / float(img_cnt))
    print "Reading in images V2 [MISSES]({0:.6f}s).".format(dur_readImages2)
    print "    Avg.Time: {0:.8f}s".format(dur_readImages2 / float(img_cnt))
    print "Reading in images V2 [HITS]({0:.6f}s).".format(dur_readImages3)
    print "    Avg.Time: {0:.8f}s".format(dur_readImages3 / float(img_cnt))

    print "\nEstimated ImageCache size (bytes):", img_cache._size
    print "    In MB: {0}".format(img_cache._size / 1e6)

    print "==== Infinite Looping Now ===="
    while True:
        pass

def test_bounded(imgsdir, imgsdir2, sizecap):
    """ A simple set of tests to sanity check cache behavior for bounded
    cache sizes.
    """
    img_cache = ImageCache(SIZECAP=sizecap,
                           img_format=IM_FORMAT_SCIPY,
                           img_mode=IM_MODE_UNCHANGED)
    
    t = time.time()
    img_cnt = 0
    for dirpath, dirnames, filenames in os.walk(imgsdir):
        for imgname in [f for f in filenames if f.lower().endswith('.png')]:
            imgpath = os.path.join(dirpath, imgname)
            (img, _imgpath), isHit = img_cache.load(imgpath)
            if imgpath != _imgpath:
                print "imgpaths not equal!"
                pdb.set_trace()
            img_cnt += 1
    dur_loadImages = time.time() - t

    print "Done loading in images ({0:.6f}s).".format(dur_loadImages)

    t = time.time()
    for dirpath, dirnames, filenames in os.walk(imgsdir):
        for imgname in [f for f in filenames if f.lower().endswith('.png')]:
            imgpath = os.path.join(dirpath, imgname)
            (img, _imgpath), isHit = img_cache.load(imgpath)
            if imgpath != _imgpath:
                print "imgpaths not equal!"
                pdb.set_trace()
    dur_readImages = time.time() - t

    t = time.time()
    for dirpath, dirnames, filenames in os.walk(imgsdir2):
        for imgname in [f for f in filenames if f.lower().endswith(".png")]:
            imgpath = os.path.join(dirpath, imgname)
            (img, _imgpath), isHit = img_cache.load(imgpath)
            if imgpath != _imgpath:
                print "imgpaths not equal!"
                pdb.set_trace()
    dur_readImages2 = time.time() - t

    t = time.time()
    for dirpath, dirnames, filenames in os.walk(imgsdir2):
        for imgname in [f for f in filenames if f.lower().endswith(".png")]:
            imgpath = os.path.join(dirpath, imgname)
            (img, _imgpath), isHit = img_cache.load(imgpath)
            if imgpath != _imgpath:
                print "imgpaths not equal!"
                pdb.set_trace()
    dur_readImages3 = time.time() - t

    print "==== Done ===="

    print "Loading in images ({0:.6f}s).".format(dur_loadImages)
    print "    Avg.Time: {0:.8f}s".format(dur_loadImages / float(img_cnt))
    print "Reading in images ({0:.6f}s).".format(dur_readImages)
    print "    Avg.Time: {0:.8f}s".format(dur_readImages / float(img_cnt))
    print "Reading in images V2 [MISSES]({0:.6f}s).".format(dur_readImages2)
    print "    Avg.Time: {0:.8f}s".format(dur_readImages2 / float(img_cnt))
    print "Reading in images V2 [HITS]({0:.6f}s).".format(dur_readImages3)
    print "    Avg.Time: {0:.8f}s".format(dur_readImages3 / float(img_cnt))

    print "\nEstimated ImageCache size (bytes):", img_cache._size
    print "    In MB: {0}".format(img_cache._size / 1e6)

    print "==== Infinite Looping Now ===="
    while True:
        pass

def test_binarydata(imgdataP, imgdims, sizecap=None):
    """ Test the binary data loading routines. """
    if sizecap == None:
        sizecap = SIZECAP_UNBOUNDED = -1

    w, h = imgdims
    nbytes = os.path.getsize(imgdataP)
    numtargets = nbytes / (w * h)
    
    img_cache = ImageCache(SIZECAP=sizecap,
                           img_format=IM_FORMAT_BINARYDATA,
                           img_mode=IM_MODE_GRAYSCALE)
    img_cache.register_binarydat(imgdataP, imgdims)
    t = time.time()
    for i in xrange(numtargets):
        img_cache.load_binarydat(i, imgdataP)
    dur_loadImages = time.time() - t

    print "Done loading in images ({0:.6f}s).".format(dur_loadImages)

    t = time.time()
    for i in xrange(numtargets):
        (img, (idx, dataP)), isHit = img_cache.load_binarydat(i, imgdataP)
        if idx != i:
            print "WOAH, retrieved wrong index?"
            pdb.set_trace()
        if dataP != imgdataP:
            print "WOAH, wrong dataP?"
            pdb.set_trace()
    dur = time.time() - t
    print "Loaded in images again. ({0:.6f}s)".format(dur)

    print "\nEstimated ImageCache size (bytes):", img_cache._size
    print "    In MB: {0}".format(img_cache._size / 1e6)

    print "==== Infinite Looping Now ===="
    while True:
        pass
    
"""
ekim@byrd:~/opencount/opencount/grouping$ python image_cache.py --sizecap 1 ../ek_tests/_img ../ek_tests/_imgCv/
================
==== Trying ImageCache.sizecap=1MB
================
Done loading in images (2.602242s).
==== Done ====
Loading in images (2.602242s).
    Avg.Time: 0.00026022s
Reading in images (2.607370s).
    Avg.Time: 0.00026074s
Reading in images V2 [MISSES](2.211290s).
    Avg.Time: 0.00022113s
Reading in images V2 [HITS](2.213054s).
    Avg.Time: 0.00022131s

Estimated ImageCache size (bytes): 976800
    In MB: 0.9768
==== Infinite Looping Now ====

================
==== Trying ImageCache.sizecap=325MB
================
Done loading in images (2.697531s).
==== Done ====
Loading in images (2.697531s).
    Avg.Time: 0.00026975s
Reading in images (2.708612s).
    Avg.Time: 0.00027086s
Reading in images V2 [MISSES](2.298018s).
    Avg.Time: 0.00022980s
Reading in images V2 [HITS](2.340966s).
    Avg.Time: 0.00023410s

Estimated ImageCache size (bytes): 324981360
    In MB: 324.98136
==== Infinite Looping Now ====

================
==== Trying ImageCache UNBOUNDED
================
Done loading in images (2.625616s).
==== Done ====
Loading in images (2.625616s).
    Avg.Time: 0.00026256s
Reading in images (0.051736s).
    Avg.Time: 0.00000517s
Reading in images V2 [MISSES](2.235135s).
    Avg.Time: 0.00022351s
Reading in images V2 [HITS](0.050173s).
    Avg.Time: 0.00000502s

Estimated ImageCache size (bytes): 651200000
    In MB: 651.2
==== Infinite Looping Now ====
"""

def main():
    args = sys.argv[1:]
    imgsdir = args[-2]
    imgsdir2 = args[-1]

    if not os.path.exists(imgsdir) and '--binary' not in args:
        print "Fatal Error: Directory doesn't exist:", imgsdir
        return 1
    if not os.path.exists(imgsdir2) and '--binary' not in args:
        print "Fatal Error: Directory dosn't exist:", imgsdir2
        return 1

    if '--debug' in args:
        global DEBUG
        DEBUG = True
    try:
        dataP = args[args.index('--binary')+1]
        w = int(args[args.index('--binary')+2])
        h = int(args[args.index('--binary')+3])
    except:
        dataP, w, h = None, None, None
        
    try:
        sizecap = int(args[args.index('--sizecap')+1])
    except:
        sizecap = None

    t = time.time()
    if dataP != None:
        print "================"
        print "==== Trying ImageCache.sizecap={0}MB, BINARYDATA".format(sizecap)
        print "================"
        test_binarydata(dataP, (w,h), sizecap=sizecap)
    elif sizecap != None:
        print "================"
        print "==== Trying ImageCache.sizecap={0}MB".format(sizecap)
        print "================"
        test_bounded(imgsdir, imgsdir2, sizecap)
    else:
        print "================"
        print "==== Trying ImageCache UNBOUNDED"
        print "================"
        test_unbounded(imgsdir, imgsdir2)

    dur_total = time.time() - t

    print "Total Time: {0:.4f}s".format(dur_total)

if __name__ == '__main__':
    main()
