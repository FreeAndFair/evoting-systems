import sys, os, threading, multiprocessing, math, traceback
sys.path.append('../')
import wx

IMPORT_STRAIGHTENER_FAIL = False
try:
    import straightener
except ImportError as e:
    print """Error importing straightener.py. 
Perhaps it is not installed. 
See installation instructions at:
http://code.google.com/p/straightener/"""
    print e
    IMPORT_STRAIGHTENER_FAIL = True

import util
from os.path import join as pathjoin
from wx.lib.pubsub import Publisher
from specify_voting_targets import util_gui as util_gui

# Global vars job_ids for the MyGauge instances
BLANKBALLOT_JOB_ID = util.GaugeID('BlankBallotStraightenerID')
VOTEDBALLOT_JOB_ID = util.GaugeID('VotedBallotStraightenerID')

def straighten_images_process(imgpaths, imgsdir, outdir, queue, size):
    """
    A function (intended to be called from another process) that
    straightens all images in imgpaths.
    Input:
        list imgpaths
        str imgsdir: The root directory of the original image directory
        str outdir: The root directory of the output images
        obj queue: A Queue instance used for IPC
        tuple size: If given, the size of the output images.
    """
    try:
        imgsdir = os.path.abspath(imgsdir)
        for imgpath in imgpaths:
            # do straighten
            imgpath = os.path.abspath(imgpath)
            prefix = os.path.normpath(os.path.commonprefix((imgsdir, imgpath)))
            if '/' != prefix[-1]:
                # commonprefix won't include the trailing '/' for directories
                prefix = prefix + '/'
            rel = os.path.normpath(imgpath[len(prefix):])
            outpath = pathjoin(outdir, rel)
            util_gui.create_dirs(os.path.split(outpath)[0])
            outpath_png = os.path.splitext(outpath)[0] + '.png'
            straightener.straighten_image(imgpath, outpath_png, imgsize=size)
            #straightener.straighten_image(imgpath, outpath, imgsize=size)
            queue.put('Done with: {0}'.format(imgpaths))
    except Exception as e:
        print "==== Process died due to exception:", e
        traceback.print_stack()
        queue.put("died")
        exit(1)
    return 0
    
def get_images_gen(imgsdir):
    for dirpath, dirnames, filenames in os.walk(imgsdir):
        for imgname in [f for f in filenames if util_gui.is_image_ext(f)]:
            yield imgname
    raise StopIteration

def divy_images(imgsdir, num):
    count = 0
    result = []
    for dirpath, dirnames, filenames in os.walk(imgsdir):
        if count >= num:
            yield result
            result = []
            count = 0
        for imgname in [f for f in filenames if util_gui.is_image_ext(f)]:
            if count >= num:
                yield result
                result = []
                count = 0
            result.append(pathjoin(dirpath, imgname))
            count +=1
    if result:
        yield result
    raise StopIteration
                
def spawn_jobs(imgsdir, outdir, num_imgs, queue, size=None):
    n_procs = float(multiprocessing.cpu_count())
    print 'cpu count:', n_procs
    imgs_per_proc = int(math.ceil(num_imgs / n_procs))
    print 'cpu count: {0} total number of imgs: {1} imgs_per_proc: {2}'.format(n_procs, num_imgs, imgs_per_proc)
    pool = multiprocessing.Pool()

    for i, imgpaths in enumerate(divy_images(imgsdir, imgs_per_proc)):
        print 'Process {0} got {1} imgs'.format(i, len(imgpaths))
        foo = pool.apply_async(straighten_images_process, args=(imgpaths, imgsdir, outdir, queue, size))
    pool.close()
    pool.join()

def start_straightening(imgsdir, outdir, num_imgs, queue, size=None):
    """
    Kicks off the straightening by spawning a 'master' process which
    spawns child worker processes.
    """
    print "Spawning master process to start straightening images in", imgsdir
    #logger = multiprocessing.log_to_stderr()
    #logger.setLevel(logging.INFO)

    p = multiprocessing.Process(target=spawn_jobs, args=(imgsdir, outdir, num_imgs, queue, size))
    p.start()

class StraightenThread(threading.Thread):
    def __init__(self, imgsdir, project, num_tasks, outdir=None, job_id=None, *args, **kwargs):
        threading.Thread.__init__(self, *args, **kwargs)
        self.imgsdir = imgsdir
        self.project = project
        self.num_tasks = num_tasks
        if not outdir:
            self.outdir = os.path.join(project.projdir_path, 'straightened_imgs')
        else:
            self.outdir = outdir
        self.job_id = job_id

    def run(self):
        if IMPORT_STRAIGHTENER_FAIL:
            print "==== Notice -- because the unrotating code was unable \
to be imported, no unrotating will happen during this run which, while it \
might be fine at this early stage, eventually other components will \
depend on straightening being done, making it imperative that the \
code be correctly imported."
            if wx.App.IsMainLoopRunning():
                wx.CallAfter(Publisher().sendMessage,
                             "signals.MyGauge.done",
                             (self.job_id,))
            return
        elif is_there_image(self.outdir):
            # Current simple thing: if there's at least one image in the
            # output directory, assume that straightening has been done
            # already, so don't do it again.
            print "BallotStraightener thinks that images in {0} has \
already been straightened, so straightening will not be run. If this \
isn't the case (i.e. if you terminated the previous straightening \
in a previous session), then remove all images in {1}".format(self.imgsdir, self.outdir)
            if wx.App.IsMainLoopRunning():
                wx.CallAfter(Publisher().sendMessage,
                             "signals.MyGauge.nextjob",
                             (self.num_tasks, self.job_id))
                wx.CallAfter(Publisher().sendMessage, 
                             "signals.MyGauge.done",
                             (self.job_id,))
            return

        if wx.App.IsMainLoopRunning():
            wx.CallAfter(Publisher().sendMessage,
                         "signals.MyGauge.nextjob",
                         (self.num_tasks, self.job_id))
        manager = multiprocessing.Manager()
        queue = manager.Queue()
        start_straightening(self.imgsdir, self.outdir, self.num_tasks, queue, size=self.project.imgsize)
        count = 0
        while True:
            if count >= self.num_tasks:
                break
            else:
                # signal tick
                foo = queue.get(block=True, timeout=None)
                if foo == 'died':
                    print" == Fatal Error: I detected that a subprocess \
died. You should probably exit."
                if wx.App.IsMainLoopRunning():
                    wx.CallAfter(Publisher().sendMessage, 
                                 "signals.MyGauge.tick",
                                 (self.job_id,))
                count += 1
        if wx.App.IsMainLoopRunning():
            wx.CallAfter(Publisher().sendMessage,
                         "signals.MyGauge.done",
                         (self.job_id,))

def is_there_image(dir):
    """
    Return True if there exists at least one image in this directory
    (will recursively search).
    """
    for dirpath, dirnames, filenames in os.walk(dir):
        if [f for f in filenames if util_gui.is_image_ext(f)]:
            return True
    return False

def do_main():
    args = sys.argv
    imgsdir = args[1]
    if len(args) <= 1:
        outdir = 'straighten_ballots_outdir'
    else:
        outdir = args[2]
    
if __name__ == '__main__':
    do_main()
