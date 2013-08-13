import sys, os, threading, multiprocessing, math, array, time, shutil, cProfile, pdb
try:
    import cPickle as pickle
except ImportError:
    import pickle
from os.path import join as pathjoin

import wx
import cv, numpy as np
from wx.lib.pubsub import Publisher

sys.path.append('..')

import util, config
import threshold.imageFile as imageFile
import pixel_reg.doExtract as doExtract
import quarantine.quarantinepanel as quarantinepanel
import grouping.run_grouping as run_grouping

class TargetExtractPanel(wx.Panel):
    def __init__(self, parent, *args, **kwargs):
        wx.Panel.__init__(self, parent, *args, **kwargs)
        
        self.init_ui()

    def init_ui(self):
        self.btn_run = wx.Button(self, label="Run Target Extraction...")
        self.btn_run.Bind(wx.EVT_BUTTON, self.onButton_run)
        txt = wx.StaticText(self, label="...Or, if you've already run Target \
Extraction, but you just want to create the Image File:")
        txt.Hide()
        btn_createImageFile = wx.Button(self, label="Advanced: Only create Image File...")
        btn_createImageFile.Bind(wx.EVT_BUTTON, self.onButton_createImageFile)
        if not config.IS_DEV:
            btn_createImageFile.Hide()
        btn_sizer = wx.BoxSizer(wx.HORIZONTAL)
        btn_sizer.Add(self.btn_run)

        self.txt_can_move_on = wx.StaticText(self, label="Target Extraction computation complete. You may move on.")
        self.txt_can_move_on.Hide()

        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.sizer.Add(btn_sizer)
        self.sizer.Add((0, 50))
        self.sizer.Add(txt)
        self.sizer.Add(btn_createImageFile)
        self.sizer.Add((0, 50))
        self.sizer.Add(self.txt_can_move_on)
        self.SetSizer(self.sizer)
        self.Layout()

    def start(self, proj):
        self.proj = proj

    def stop(self):
        pass

    def onButton_run(self, evt):
        self.Disable()

        # First, remove all files
        if os.path.exists(self.proj.extracted_dir): shutil.rmtree(self.proj.extracted_dir)
        if os.path.exists(self.proj.extracted_metadata): shutil.rmtree(self.proj.extracted_metadata)
        if os.path.exists(self.proj.ballot_metadata): shutil.rmtree(self.proj.ballot_metadata)
        if os.path.exists(pathjoin(self.proj.projdir_path, self.proj.targetextract_quarantined)):
            os.remove(pathjoin(self.proj.projdir_path, self.proj.targetextract_quarantined))
        if os.path.exists(pathjoin(self.proj.projdir_path, "extracted_radix")): 
            shutil.rmtree(pathjoin(self.proj.projdir_path, "extracted_radix"))
        if os.path.exists(pathjoin(self.proj.projdir_path, "extracted_diffs")):
            shutil.rmtree(pathjoin(self.proj.projdir_path, "extracted_diffs"))
        if os.path.exists(pathjoin(self.proj.projdir_path, "targetextract_avg_intensities.p")):
            os.remove(pathjoin(self.proj.projdir_path, "targetextract_avg_intensities.p"))
        if os.path.exists(pathjoin(self.proj.projdir_path, self.proj.ballot_to_targets)):
            os.remove(pathjoin(self.proj.projdir_path, self.proj.ballot_to_targets))
        if os.path.exists(self.proj.classified):
            os.remove(self.proj.classified)
        if os.path.exists(self.proj.extractedfile):
            os.remove(self.proj.extractedfile)
        if os.path.exists(self.proj.extractedfile+".type"):
            os.remove(self.proj.extractedfile+".type")
        if os.path.exists(self.proj.extractedfile+".size"):
            os.remove(self.proj.extractedfile+".size")
        if os.path.exists(self.proj.threshold_internal):
            os.remove(self.proj.threshold_internal)

        t = RunThread(self.proj)
        t.start()

        gauge = util.MyGauge(self, 5, tofile=self.proj.timing_runtarget,
                             ondone=self.on_targetextract_done, thread=t)
        gauge.Show()

    def onButton_createImageFile(self, evt):
        self.Disable()
        t = RunThread(self.proj, skip_extract=True)
        t.start()

        gauge = util.MyGauge(self, 4, tofile=self.proj.timing_runtarget,
                             ondone=self.on_targetextract_done, thread=t)
        gauge.Show()

    def on_targetextract_done(self):
        print "...TargetExtraction Done!..."
        self.btn_run.Disable()
        self.txt_can_move_on.Show()
        self.Layout()
        self.Enable()

class RunThread(threading.Thread):
    def __init__(self, proj, skip_extract=False, do_profile=False, profile_out='profile_targetextract.out', *args, **kwargs):
        threading.Thread.__init__(self, *args, **kwargs)
        self.proj = proj
        self.skip_extract = skip_extract
        self.do_profile = do_profile
        self.profile_out = profile_out

    def run(self):
        if self.do_profile:
            cProfile.runctx('self.do_target_extract()', {}, {'self': self}, self.profile_out)
        else:
            self.do_target_extract()

    def do_target_extract(self):
        if config.TIMER:
            config.TIMER.start_task("TargetExtract_DoTargetExtract_CPU")
        if not self.skip_extract:
            group_to_ballots = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                         self.proj.group_to_ballots), 'rb'))
            group_exmpls = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                     self.proj.group_exmpls), 'rb'))
            b2imgs = pickle.load(open(self.proj.ballot_to_images, 'rb'))
            img2b = pickle.load(open(self.proj.image_to_ballot, 'rb'))
            img2page = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                 self.proj.image_to_page), 'rb'))
            img2flip = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                 self.proj.image_to_flip), 'rb'))
        target_locs_map = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                    self.proj.target_locs_map), 'rb'))
            
        totalTime = time.time()
        time_doExtract = time.time()
        print "...starting doExtract..."
        if not self.skip_extract:
            qballotids = quarantinepanel.get_quarantined_ballots(self.proj)
            discarded_ballotids = quarantinepanel.get_discarded_ballots(self.proj)
            ioerr_ballotids = run_grouping.get_ioerr_bals(self.proj)
            bad_ballotids = list(set(qballotids + discarded_ballotids + ioerr_ballotids))
            nProc = 1 if self.do_profile else None
            # list AVG_INTENSITIES: [(str targetid, float avg_intensity), ...]
            #     where TARGETID :=  str(balId)+"\0"+str(page)+"\0"+str(int(uid))
            avg_intensities, bal2targets = doExtract.extract_targets(group_to_ballots, b2imgs, img2b, img2page, img2flip,
                                                                     target_locs_map, group_exmpls,
                                                                     bad_ballotids,
                                                                     self.proj.extracted_dir,
                                                                     self.proj.extracted_metadata,
                                                                     self.proj.ballot_metadata,
                                                                     pathjoin(self.proj.projdir_path,
                                                                              self.proj.targetextract_quarantined),
                                                                     self.proj.voteddir,
                                                                     self.proj.projdir_path,
                                                                     nProc=nProc,
                                                                     method_galign=doExtract.GALIGN_NORMAL,
                                                                     method_lalign=doExtract.LALIGN_NORMAL)
            pickle.dump(avg_intensities, open(pathjoin(self.proj.projdir_path,
                                                       'targetextract_avg_intensities.p'), 'wb'),
                        pickle.HIGHEST_PROTOCOL)
            pickle.dump(bal2targets, open(pathjoin(self.proj.projdir_path,
                                                   self.proj.ballot_to_targets), 'wb'),
                        pickle.HIGHEST_PROTOCOL)
        else:
            avg_intensities = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                        'targetextract_avg_intensities.p'), 'rb'))
            bal2targets = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                    self.proj.ballot_to_targets), 'rb'))
            print "    (skip_extract was True - not running doExtract)"
        dur_doExtract = time.time() - time_doExtract
        print "...Finished doExtract ({0} s)...".format(dur_doExtract)
        if config.TIMER:
            config.TIMER.stop_task("TargetExtract_DoTargetExtract_CPU")
        print "...Doing post-target-extraction work..."
        time_post = time.time()

        if config.TIMER:
            config.TIMER.start_task("TargetExtract_DoPostWork_CPU")

        total = len(bal2targets)

        del bal2targets ## Try to reclaim some memory

        manager = multiprocessing.Manager()
        queue = manager.Queue()
        time_doandgetAvg = time.time()

        if wx.App.IsMainLoopRunning():
            wx.CallAfter(Publisher().sendMessage, "signals.MyGauge.nextjob", total)
        fulllst = sorted(avg_intensities, key=lambda x: x[1])  # sort by avg. intensity

        del avg_intensities ## Try to reclaim some memory

        fulllst = [(x,int(y)) for x,y in fulllst]
        
        time_classifiedWrite = time.time()

        out = open(self.proj.classified, "w")
        # Store imgpath \0 avg_intensity to output file OUT
        for a,b in fulllst:
            out.write(a + "\0" + str(b) + "\n")
        out.close()

        dur_classifiedWrite = time.time() - time_classifiedWrite

        print "...Starting imageFileMake..."
        time_imageFileMake = time.time()

        def get_target_size():
            # TARGET_LOCS_MAP: maps {int groupID: {int page: [CONTEST_i, ...]}}, where each
            #     CONTEST_i is: [contestbox, targetbox_i, ...], where each
            #     box := [x1, y1, width, height, id, contest_id]
            widgh, height = None, None
            for groupid, pagedict in target_locs_map.iteritems():
                for page, contests in pagedict.iteritems():
                    for contest in contests:
                        targetboxes = contest[1:]
                        for (x1,y1,w,h,id,contest_id) in targetboxes:
                            return w, h
            return None, None

        w, h = get_target_size()
        if w == None:
            raise Exception("Woah, No targets in this election??")

        imageFile.makeOneFile(fulllst, 
                              pathjoin(self.proj.projdir_path,'extracted_radix/'),
                              self.proj.extractedfile,
                              (w,h),
                              SORT_METHOD=imageFile.METHOD_DYN,
                              MEM_C=0.6)
        dur_imageFileMake = time.time() - time_imageFileMake
        print "...Finished imageFileMake ({0} s).".format(dur_imageFileMake)

        if config.TIMER:
            config.TIMER.stop_task("TargetExtract_DoPostWork_CPU")

        if wx.App.IsMainLoopRunning():
            wx.CallAfter(Publisher().sendMessage, "broadcast.rundone")
            wx.CallAfter(Publisher().sendMessage, "signals.MyGauge.done")
        
        dur_post = time.time() - time_post
        print "...Finished post-target-extraction work ({0} s).".format(dur_post)
        dur_totalTime = time.time() - totalTime
        
        print "...Finished Target Extraction. ({0} s).".format(dur_totalTime)
        frac = (dur_doExtract / dur_totalTime) * 100
        print "    doExtract: {0:.3f}%  |  {1:.3f} s".format(frac, dur_doExtract)
        frac = (dur_post / dur_totalTime) * 100
        print "    post-work: {0:.3f}%  |  {1:.3f} s".format(frac, dur_post)
        frac = (dur_classifiedWrite / dur_post) * 100
        print "        classifiedWrite: {0:.3f}%  |  {1:.3f} s".format(frac, dur_classifiedWrite)
        frac = (dur_imageFileMake / dur_post) * 100
        print "        imageFileMake: {0:.3f}%   |  {1:.3f} s".format(frac, dur_imageFileMake)

def start_doandgetAvg(queue, rootdir, dirList):
    p = multiprocessing.Process(target=spawn_jobs, args=(queue, rootdir, dirList))
    p.start()

def doandgetAvgs(imgnames, rootdir, queue):
    for imgname in imgnames:
        imgpath = pathjoin(rootdir, imgname)
        I = cv.LoadImage(imgpath, cv.CV_LOAD_IMAGE_GRAYSCALE)
        w, h = cv.GetSize(I)
        result = cv.Sum(I)[0] / float(w*h)
        #data = shared.standardImread(pathjoin(rootdir, imgname), flatten=True)
        #result = 256 * (float(sum(map(sum, data)))) / (data.size)
        queue.put((imgname, result))
    return 0

def spawn_jobs(queue, rootdir, dirList):
    def divy_elements(lst, k):
        """ Separate lst into k chunks """
        if len(lst) <= k:
            return [lst]
        chunksize = math.floor(len(lst) / float(k))
        i = 0
        chunks = []
        curchunk = []
        while i < len(lst):
            if i != 0 and ((i % chunksize) == 0):
                chunks.append(curchunk)
                curchunk = []
            curchunk.append(lst[i])
            i += 1
        if curchunk:
            chunks.append(curchunk)
        return chunks
    pool = multiprocessing.Pool()
    n_procs = float(multiprocessing.cpu_count())
    for i, imgpaths in enumerate(divy_elements(dirList, n_procs)):
        print 'Process {0} got {1} imgs'.format(i, len(imgpaths))
        pool.apply_async(doandgetAvgs, args=(imgpaths, rootdir, queue))
    pool.close()
    pool.join()

def _run_target_extract(proj, do_profile, profile_out):
    if os.path.exists(proj.extracted_dir): shutil.rmtree(proj.extracted_dir)
    if os.path.exists(proj.extracted_metadata): shutil.rmtree(proj.extracted_metadata)
    if os.path.exists(proj.ballot_metadata): shutil.rmtree(proj.ballot_metadata)
    if os.path.exists(pathjoin(proj.projdir_path, proj.targetextract_quarantined)):
        os.remove(pathjoin(proj.projdir_path, proj.targetextract_quarantined))
    if os.path.exists(pathjoin(proj.projdir_path, "extracted_radix")): 
        shutil.rmtree(pathjoin(proj.projdir_path, "extracted_radix"))
    if os.path.exists(pathjoin(proj.projdir_path, "extractedfile")):
        os.remove(pathjoin(proj.projdir_path, "extractedfile"))
    if os.path.exists(pathjoin(proj.projdir_path, "extractedfile.size")):
        os.remove(pathjoin(proj.projdir_path, "extractedfile.size"))
    if os.path.exists(pathjoin(proj.projdir_path, "extractedfile.type")):
        os.remove(pathjoin(proj.projdir_path, "extractedfile.type"))

    t = RunThread(proj, do_profile=do_profile, profile_out=profile_out)
    t.start()
    t.join()
    
def main():
    args = sys.argv[1:]
    projdir = args[-1]
    do_profile = '--profile' in args
    try:
        N = int(args[args.index('-n')+1])
    except:
        N = 3
    try:
        profile_out = args[args.index('--profile')+1]
        print "Profiling with cProfile -> {0}".format(profile_out)
        N = 1 # Only profile once
    except:
        profile_out = None
    print "    (Best of {0} trials)".format(N)
    proj = pickle.load(open(pathjoin(projdir, 'proj.p')))
    os.chdir('..')
    times = []
    for i in xrange(N):
        t = time.time()
        _run_target_extract(proj, do_profile, profile_out)
        dur = time.time() - t
        times.append(dur)
    tot_time = sum(times)
    print "Total Time: {0:.6f}s (Out of {1} trials)".format(tot_time, N)
    print "    Mean   : {0:.8f}s".format(np.mean(times))
    print "    Std.Dev: {0:.8f}s".format(np.std(times))
    
    print "Done."

if __name__ == '__main__':
    main()
