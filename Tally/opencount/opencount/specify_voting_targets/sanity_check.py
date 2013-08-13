import os, time, math
from optparse import OptionParser
import Image, cv
import wx
from wx.lib.pubsub import Publisher

BIN_SIZE = 10000

EVT_SANITYCHECK_ID = wx.NewId()

def EVT_SANITYCHECK(win, fn):
    win.Connect(-1, -1, EVT_SANITYCHECK_ID, fn)

class SanityCheckEvent(wx.PyEvent):
    def __init__(self, data):
        """
        data := (str 'templates'/'samples', dict)
        """
        wx.PyEvent.__init__(self)
        self.SetEventType(EVT_SANITYCHECK_ID)
        self.data = data

def sanity_check(templatesdir, samplesdir, frame):
    _,_,_,_,_,_,will_skip = collect_stats(templatesdir)
    wx.PostEvent(frame, SanityCheckEvent(('templates', will_skip)))
    _,_,_,_,_,_,will_skip2 = collect_stats(samplesdir)
    wx.PostEvent(frame, SanityCheckEvent(('samples', will_skip2)))
    wx.CallAfter(Publisher().sendMessage, "signals.ProgressGauge.done")

def safe_open(image_path):
    try:
        #return Image.open(image_path) 
        return cv.LoadImage(image_path)
    except IOError:
        return None

def collect_stats(dir):
    """
    0: files_processed - # of files examined
    1: images - # of images in examined
    2: image_sizes - hash of number of files in a given size range, 100kb bins
    3: image_formats - hash of number of files of each seen format
    4: image_modes - hash of number of files of each seen mode
    5: non_image_files - list of all non-image files examined
    """
    files_processed = 0
    images = 0
    image_sizes = {}
    image_formats = {}
    image_modes = {}
    non_image_files = []
    will_skip = {}
    
    for dirpath, dirnames, filenames in os.walk(dir):
        for f in filenames:
            files_processed += 1
            imgpath = os.path.join(dirpath, f)
            
            # Try to open the file as an image
            img = safe_open(imgpath)
            if img != None:
                images += 1
                
                # Bin the image sizes by 10kb
                size = os.path.getsize(imgpath)
                size /= BIN_SIZE
                size = math.floor(size)
                if not image_sizes.has_key(size):
                    image_sizes[size] = 0
                image_sizes[size] += 1
                
                # Record the format of the image
                #format = img.format
                #if not image_formats.has_key(format):
                #    image_formats[format] = 0
                #image_formats[format] += 1
                
                # Record the mode of the image
                #mode = img.mode
                #if not image_modes.has_key(mode):
                #    image_modes[mode] = 0
                #image_modes[mode] += 1
            else:
                non_image_files.append(f)
                will_skip[imgpath.replace(dir,'')[1:]] = 'not an image'
            wx.CallAfter(Publisher().sendMessage, "signals.ProgressGauge.tick")
    return files_processed, images, image_sizes, image_formats, image_modes, non_image_files, will_skip

if __name__ == "__main__":
    """
    Run a sanity check on the template and sample files before proceeding
    """
    
    parser = OptionParser()
    parser.add_option("-t", "--temp_dir", dest="template_dir",
                      help="Path to folder containing template images")
    parser.add_option("-s", "--samp_dir", dest="sample_dir",
                      help="Path to folder containing sample images")
    (options, args) = parser.parse_args()
    
    if not options.template_dir or not options.sample_dir:
        print """Must specify directories, i.e.:
        
    $ python quick_overlay.py -t templates -s samples"""
        exit(1)
    
    temp_dir = os.path.join(options.template_dir)
    samp_dir = os.path.join(options.sample_dir)
    
    start_time = time.time()
    files_processed, images, image_sizes, image_formats, image_modes, non_image_files, will_skip = collect_stats(temp_dir)
    
    print "==== Files Processed: {0}".format(files_processed)
    print "==== Images Found:    {0}".format(images)
    print "==== Images per Sizes:"
    for size in image_sizes.keys():
        print "\t{0}-{1}kb:\t{2} files".format(int(size*(BIN_SIZE/1000)), int((size+1)*(BIN_SIZE/1000)), image_sizes[size])
    print "==== Images per Format"
    for format in image_formats.keys():
        print "\t{0}:\t{1} files".format(format, image_formats[format])
    print "==== Images per Mode"
    for mode in image_modes.keys():
        print "\t{0}:\t{1} files".format(mode, image_modes[mode])
    print "==== Non-Image Files: {0}".format(len(non_image_files))
    
    run_time = time.time() - start_time
    print "==== Elapsed Time:    {0}".format(run_time)
    if files_processed > 0:
        print "==== Time per File:   {0}".format(run_time/files_processed)
    
    start_time = time.time()
    files_processed, images, image_sizes, image_formats, image_modes, non_image_files, will_skip = collect_stats(samp_dir)
    
    print "==== Files Processed: {0}".format(files_processed)
    print "==== Images Found:    {0}".format(images)
    print "==== Images per Sizes:"
    for size in image_sizes.keys():
        print "\t{0}-{1}kb:\t{2} files".format(int(size*(BIN_SIZE/1000)), int((size+1)*(BIN_SIZE/1000)), image_sizes[size])
    print "==== Images per Format"
    for format in image_formats.keys():
        print "\t{0}:\t{1} files".format(format, image_formats[format])
    print "==== Images per Mode"
    for mode in image_modes.keys():
        print "\t{0}:\t{1} files".format(mode, image_modes[mode])
    print "==== Non-Image Files: {0}".format(len(non_image_files))
    
    run_time = time.time() - start_time
    print "==== Elapsed Time:    {0}".format(run_time)
    if files_processed > 0:
        print "==== Time per File:   {0}".format(run_time/files_processed)
