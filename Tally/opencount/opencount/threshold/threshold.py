import pdb, traceback
import sys
import wx
import os
from os.path import join as pathjoin

from PIL import Image, ImageDraw

from time import time
import imageFile
import array
try: import cPickle as pickle
except: import pickle
import math
import csv

import numpy as np
import wx.lib
import wx.lib.dialogs

sys.path.append('..')
import util, config
from util import is_image_ext, pil2wxb, MyGauge
import ViewOverlays

class OverlayGrid(wx.Frame):
    def __init__(self, parent, maybefilled, maybeunfilled):
        wx.Frame.__init__(self, parent, size=(800,800))

        sizer = wx.BoxSizer(wx.VERTICAL)
        self.parent = parent
        self.maybefilled = maybefilled
        self.maybeunfilled = maybeunfilled

        bit = self.createImages(np.max, 90, maybefilled)

        for i in range(0,len(bit),10):
            s2 = wx.BoxSizer(wx.HORIZONTAL)
            for each in bit[i:i+10]:
                s2.Add(each)
            sizer.Add(s2)

        bit = self.createImages(np.min, 90, maybeunfilled)

        for i in range(0,len(bit),10):
            s2 = wx.BoxSizer(wx.HORIZONTAL)
            for each in bit[i:i+10]:
                s2.Add(each)
            sizer.Add(s2)

        self.SetSizer(sizer)

    def createImages(self, fn, numImgs, whichside):
        parent = self.parent
        results = []
        print "GO UP TO", len(whichside)
        gap = int(math.floor(float(len(whichside))/numImgs))
        for i in range(0,len(whichside),gap):
            print i, gap
            # BOUNDRY ERROR
            use_imgs,ch = parent.imagefile.readManyImages_filter(whichside[i:i+gap], parent.numcols, 
                                                                 parent.basetargetw, parent.basetargeth,
                                                                 parent.targetw, parent.targeth, True)

            if ch == True:
                res = np.uint8(np.round(fn(np.array(use_imgs),axis=0)))
                res = (res,res,res)
            else:
                res = [np.uint8(np.round(fn(np.array(use_imgs[i::3]),axis=0))) for i in range(3)]
            args = [Image.fromarray(x.reshape((parent.targeth,parent.targetw))) for x in res]
            resimg = Image.merge('RGB', tuple(args))
            
            results.append(wx.StaticBitmap(self, -1, pil2wxb(resimg)))

        return results


class GridShow(wx.ScrolledWindow):
    """
    Class that displays voting targets
    """
    threshold = None
    # dict WRONG: {int idx: bool True}
    #     Stores indices for all targets that the user marked as being
    #     'wrong'. When generating the target interpretations, targets
    #     that lie before the threshold line that are also in WRONG are
    #     marked as 'EMPTY'. Targets that lie after the threshold but
    #     are in WRONG are marked as 'FULL'.
    wrong = {}
    jpgs = {}
    basejpgs = {}
    images = {}
    numcols = 20

    def lookupFullList(self, i):
        return self.classified_file[i]

    def enumerateOverFullList(self, force=False):
        for target,fill in self.classified_file:
            yield (target,fill)

    def target_to_sample(self, targetpath):
        return self.bal2imgs[targetpath[0]][targetpath[1]]

    def get_meta(self, ballotid, page):
        if page not in self.bal2targets[ballotid]:
            _,_, imgmeta_path = self.bal2targets[ballotid].values()[0]
        else:
            _,_, imgmeta_path = self.bal2targets[ballotid][page]
        return pickle.load(open(imgmeta_path, 'rb'))

    def sample_to_targets(self, ballotpath):
        page = self.img2page[ballotpath]
        ballotid = self.img2bal[ballotpath]
        return self.get_meta(ballotid, page)['targets']

    def sample_to_target_bboxes(self, ballotpath):
        page = self.img2page[ballotpath]
        ballotid = self.img2bal[ballotpath]
        return self.get_meta(ballotid, page)['target_bboxes']

    @util.pdb_on_crash
    def lightBox(self, i, evt=None):
        # Which target we clicked on
        _t = time()

        i = self.visible_to_index[i+evt.GetPositionTuple()[0]/self.targetw]

        print "...Starting LightBox...", i

        targetpath = self.lookupFullList(i)[0]
        balid, side = targetpath[0], targetpath[1]
        imgpaths = sorted(self.bal2imgs[balid], key=lambda imP: self.img2page[imP])
        ballotpath = imgpaths[side]

        if not os.path.exists(ballotpath):
            dlg = wx.MessageDialog(self, message="Oh no. We couldn't open this ballot for some reason ...", style=wx.ID_OK)
            dlg.ShowModal()
            return

        pan = wx.Panel(self.parent, size=self.parent.thesize, pos=(0,0))

        before = Image.open(ballotpath).convert("RGB")

        dur = time() - _t
        print "    Phase 1: {0} s".format(dur)
        _t = time()

        doflip = self.img2flip[ballotpath]
        if doflip:
            before = before.rotate(180)

        if before.size[1] > self.parent.thesize[1]:
            fact = float(before.size[1])/self.parent.thesize[1]
            before = before.resize((int(before.size[0]/fact), 
                                    int(before.size[1]/fact)))
        else:
            fact = 1

        temp = before.copy()
        draw = ImageDraw.Draw(temp)

        ballotid = self.img2bal[ballotpath]
        input_target_id = targetpath[2]

        dur = time() - _t
        print "    Phase 2: {0} s".format(dur)
        _t = time()

        indexs = []
        other_stuff = [] 
        
        targetids = self.sample_to_targets(ballotpath)
        target_bboxes = self.sample_to_target_bboxes(ballotpath)
        page = self.img2page[ballotpath]

        for tid,bbox in zip(targetids,target_bboxes):
            ind = self.classified_lookup[tid]
            indexs.append(([a / fact for a in bbox], ind))
            other_stuff.append((ind, bbox, tid))

        print "    Phase 3: {0} s".format(time() - _t)
        _t = time()

        for (ind, locs, tid) in other_stuff:
            # Note to self:
            # when adding target-adjustment from here, you need to some how map
            # targetID name -> index in the list to find if it is 'wrong' or not.
            color = (0,255,0) if tid[2] == input_target_id else (0, 0, 200)
            draw.rectangle(((locs[2])/fact-1, (locs[0])/fact-1, 
                            (locs[3])/fact+1, (locs[1])/fact+1),
                           outline=color)
            draw.rectangle(((locs[2])/fact-2, (locs[0])/fact-2, 
                            (locs[3])/fact+2, (locs[1])/fact+2),
                           outline=color)
            isfilled = (ind < self.threshold)^(ind in self.wrong)
            if isfilled:
                draw.rectangle(((locs[2])/fact, (locs[0])/fact, 
                                (locs[3])/fact, (locs[1])/fact),
                               fill=(255, 0, 0))
                
        print "    Phase 4: {0} s".format(time() - _t)
        _t = time()

        img = wx.StaticBitmap(pan, -1, pil2wxb(Image.blend(before, temp, .5)))

        def markwrong(evt):
            x,y = evt.GetPositionTuple()
            for (u,d,l,r),index in indexs:
                if l <= x <= r and u <= y <= d:
                    print "IS", index
                    self.markWrong(index)

        img.Bind(wx.EVT_LEFT_DOWN, markwrong)
        def remove(x):
            pan.Destroy()

        ifflipped = "(auto-flipped)" if doflip else ""
        def lines(x):
            if len(x) < 60: return x
            return x[:60]+"\n"+lines(x[60:])

        
        templatepath = self.get_meta(self.img2bal[ballotpath], page)['template']
        wx.StaticText(pan, label="Ballot image:\n"+lines(ballotpath)+"\n\nTemplate image:\n"+lines(templatepath)+"\n\n"+ifflipped, 
                      pos=(before.size[0],before.size[1]/3))

        b = wx.Button(pan, label="Back", pos=(before.size[0], 2*before.size[1]/3))
        b.Bind(wx.EVT_BUTTON, remove)

        q = wx.Button(pan, label="Quarantine", pos=(before.size[0], 2*before.size[1]/3+50))
        q.Bind(wx.EVT_BUTTON, lambda x: self.markQuarantine(i))
        
    def addimg(self, i):
        pilimg = self.jpgs[i]
        offset = self.CalcScrolledPosition((0,0))[1]
        pos = (0, i*self.targeth/self.numcols+offset)

        #print "DRAW IMG", pilimg, pos, i
        try:
            img = wx.StaticBitmap(self, -1, pil2wxb(pilimg), pos=pos)
        except:
            traceback.print_exc()
            pdb.set_trace()
        #img.SetToolTip(wx.ToolTip(str(weight)))
        def call(im, jp, ii):
            def domark(x): 
                self.markWrong(ii, evt=x)
            img.Bind(wx.EVT_LEFT_DOWN, domark)
            
            def menu(event1):
                m = wx.Menu()
                def decide(event2):
                    item = m.FindItemById(event2.GetId())
                    text = item.GetText()
                    if text == "Set Threshold":
                        self.setLine(ii, evt=event1)
                    if text == "Open Ballot":
                        self.lightBox(ii, evt=event1)
                    if text == "Mark Row Wrong":
                        for ct in range(self.numcols):
                            self.markWrong(i+ct)

                a = m.Append(-1, "Set Threshold")
                self.Bind(wx.EVT_MENU, decide, a)
                b = m.Append(-1, "Open Ballot")
                self.Bind(wx.EVT_MENU, decide, b)
                c = m.Append(-1, "Mark Row Wrong")
                self.Bind(wx.EVT_MENU, decide, c)
                pos = event1.GetPosition()
                pos = self.ScreenToClient(pos)
                m.Bind(wx.EVT_CONTEXT_MENU, decide)
                q = self.PopupMenu(m)
            img.Bind(wx.EVT_RIGHT_DOWN, menu)
        call(img, pilimg, i)
        self.images[i] = img
        return img

    def markQuarantine(self, i, ballotpath=None):
        if ballotpath == None:
            targetpath = self.lookupFullList(i)[0]
            ballotpath = self.target_to_sample(targetpath)
        if ballotpath not in self.quarantined:
            self.quarantined.append(ballotpath)
        for each in self.sample_to_targets(ballotpath):
            if each in self.classified_lookup:
                self.markQuarantineSingle(self.classified_lookup[each])

    def markQuarantineSingle(self, i):
        self.quarantined_targets.append(i)
        rdown = i/self.numcols*self.numcols
        if rdown not in self.jpgs: return
        offset = self.CalcScrolledPosition((0,0))[1]
        
        self.somethingHasChanged = True

        jpg = self.jpgs[rdown]
        imd = ImageDraw.Draw(jpg)
        imd.rectangle((self.targetw*(i%self.numcols), 0,
                       self.targetw*(i%self.numcols)-1+self.targetw, self.targeth-1),
                      fill=(120,0,0))
        self.jpgs[rdown] = jpg

        self.images[rdown].Destroy()
        self.addimg(rdown)

        jpg = self.basejpgs[rdown]
        imd = ImageDraw.Draw(jpg)
        imd.rectangle((self.targetw*(i%self.numcols), 0,
                       self.targetw*(i%self.numcols)-1+self.targetw, self.targeth-1),
                      fill=(120,0,0))
        self.basejpgs[rdown] = jpg

        self.Refresh()

    def drawWrongMark(self, i):
        i = self.index_to_visible[i]
        imgIdx = i-i%self.numcols
        try:
            jpg = self.jpgs[imgIdx]
        except:
            traceback.print_exc()
            pdb.set_trace()
        '''
        # Old Version purely using PIL -- a bit slow
        copy = jpg.copy()
        imd = ImageDraw.Draw(copy)
        imd.rectangle((self.targetw*(i-imgIdx), 0,
                       self.targetw*(i-imgIdx)+self.targetw-1, self.targeth-1),
                      fill=(255,0,0))
        self.jpgs[imgIdx] = Image.blend(jpg, copy, .3)
        '''
        # New version that uses numpy -- not much faster.
        target_np = np.fromstring(jpg.tostring(), dtype='uint8').reshape(jpg.size[1], jpg.size[0], 3)
        x1, y1 = self.targetw * (i - imgIdx), 0
        x2, y2 = self.targetw * (i - imgIdx) + self.targetw - 1, self.targeth - 1
        
        C = 0.7
        RED = np.array([255, 0, 0], dtype='uint8')
        target_np[y1:y2, x1:x2] *= C
        target_np[y1:y2, x1:x2] += (1 - C) * RED
        target_np_pil = Image.fromarray(target_np)
        self.jpgs[imgIdx] = target_np_pil
        
        self.images[imgIdx].Destroy()
        self.addimg(imgIdx)

    def drawWrongMarks(self, idxs, C=0.7):
        """ Draws a red transparent mask on all visible targets. These
        targets are targets that the user manually marked as being 
        'wrong' (by left-clicking them).
        Input:
            list IDXS:
            float C: In range [0.0, 1.0]
                How transparent the red mask should be. 1.0 is no red,
                0.0 is completely red.
        """
        imgIdx2pilimg = {} # maps {int imgIdx: Image pilimg}
        imgIdx2idxs = {} # maps {int imgIdx: [int i0, ...]}
        RED = np.array([255, 0, 0], dtype='uint8')
        w_jpg, h_jpg = None, None
        for i in idxs:
            i_vis = self.index_to_visible[i]
            imgIdx = i_vis - (i_vis % self.numcols)
            pilimg = imgIdx2pilimg.get(imgIdx, None)
            if pilimg == None:
                pilimg = self.basejpgs[imgIdx]
                imgIdx2pilimg[imgIdx] = pilimg
            if w_jpg == None:
                w_jpg, h_jpg = pilimg.size[0], pilimg.size[1]
            imgIdx2idxs.setdefault(imgIdx, []).append(i_vis)

        for imgIdx, idxs in imgIdx2idxs.iteritems():
            pilimg = imgIdx2pilimg[imgIdx]
            row_np = np.fromstring(pilimg.tostring(), dtype='uint8').reshape(pilimg.size[1], pilimg.size[0], 3)
            for i in idxs:
                x1, y1 = self.targetw * (i - imgIdx), 0
                x2, y2 = self.targetw * (i - imgIdx) + self.targetw - 1, self.targeth - 1
                row_np[y1:y2, x1:x2] *= C
                row_np[y1:y2, x1:x2] += (1 - C) * RED
            row_pil = Image.fromarray(row_np)
            self.jpgs[imgIdx] = row_pil
            self.images[imgIdx].Destroy()
            self.addimg(imgIdx)

    def markWrong(self, which, evt=None):
        # Input which is the wrong mark in visible coordinates.
        if evt == None:
            imgIdx = which - (which%self.numcols)
        else:
            imgIdx = which
            which = which+evt.GetPositionTuple()[0]/self.targetw
            
        if imgIdx not in self.jpgs: 
            print "BAD!"
            return

        self.somethingHasChanged = True

        offset = self.CalcScrolledPosition((0,0))[1]

        converted_id = self.visible_to_index[which]
        
        if converted_id not in self.wrong:
            self.wrong[converted_id] = True
            self.drawWrongMark(converted_id)
        else:
            jpg = self.basejpgs[imgIdx].copy()
            self.jpgs[imgIdx] = jpg
            self.images[imgIdx].Destroy()
            self.addimg(imgIdx)
            del self.wrong[converted_id]
            idxs_wrong_todraw = []
            for each in self.wrong:
                if each/self.numcols == converted_id/self.numcols:
                    idxs_wrong_todraw.append(each)
            self.drawWrongMarks(idxs_wrong_todraw)
            if self.threshold != None:
                self.drawThreshold()
        self.Refresh()

    def drawThreshold(self):
        if self.threshold not in self.index_to_visible: return
        cthreshold = self.index_to_visible[self.threshold]
        imgIdx = cthreshold - (cthreshold%self.numcols)
        if not (imgIdx in self.jpgs and imgIdx in self.images): return

        take = self.jpgs[imgIdx]
        dr = ImageDraw.Draw(take)
        dr.rectangle((0, self.targeth-1, 
                      (cthreshold-imgIdx)*self.targetw, self.targeth-1),
                     fill=(0,255,0))

        dr.rectangle(((cthreshold-imgIdx)*self.targetw, 0, 
                      (cthreshold-imgIdx)*self.targetw, self.targeth-1),
                     fill=(0,255,0))

        dr.rectangle(((cthreshold-imgIdx)*self.targetw, 0, 
                      self.targetw*self.numcols, 0),
                     fill=(0,255,0))

        self.images[imgIdx].Destroy()
        self.addimg(imgIdx)
        
        self.Refresh()

    def setLine(self, which, evt=None):
        if evt == None:
            if which not in self.index_to_visible: return
            imgIdx = self.index_to_visible[which] - (self.index_to_visible[which]%self.numcols)
        else:
            imgIdx = which
            which = which+int(round(float(evt.GetPositionTuple()[0])/self.targetw))
            which = self.visible_to_index[which]
            print 'click line ', evt.GetPositionTuple()[0]/self.targetw
            
        if imgIdx not in self.jpgs: 
            print "BAD LINE!"
            return

        self.somethingHasChanged = True

        if self.threshold != None and self.threshold in self.index_to_visible:
            lastIdx = self.index_to_visible[self.threshold] - self.index_to_visible[self.threshold]%self.numcols
            if lastIdx in self.images:
                self.jpgs[lastIdx] = self.basejpgs[lastIdx].copy()
                self.images[lastIdx].Destroy()
                self.addimg(lastIdx)
            for each in self.wrong:
                if each in self.index_to_visible:
                    if self.index_to_visible[each]/self.numcols == self.index_to_visible[self.threshold]/self.numcols:
                        self.drawWrongMark(each)
            
        self.threshold = which

        self.drawThreshold()

    """
    def show_overlays(self, ii, evt):
        #Starting at the place where the user right-clicked, generate 
        #min/max overlays from all voting targets, up to the last target.
        start_idx = ii+int(round(float(evt.GetPositionTuple()[0])/self.targetw))

        print 'start_idx:', start_idx
        imgpaths = []
        for idx, (target_imgpath, id) in enumerate(self.enumerateOverFullList()):
            if idx >= start_idx:
                imgpaths.append(target_imgpath)

        frame = ViewOverlays.SimpleOverlayFrame(self, imgpaths)
        frame.Show()
    """

    def __init__(self, parent, proj):
        """
        Set things up! Yay!
        """
        wx.ScrolledWindow.__init__(self, parent, -1)

        self.proj = proj
        self.proj.addCloseEvent(self.dosave)
        self.img2bal = pickle.load(open(proj.image_to_ballot, 'rb'))
        self.bal2imgs = pickle.load(open(proj.ballot_to_images, 'rb'))
        self.img2page = pickle.load(open(pathjoin(proj.projdir_path, proj.image_to_page), 'rb'))
        self.img2flip = pickle.load(open(pathjoin(proj.projdir_path, proj.image_to_flip), 'rb'))
        self.bal2targets = pickle.load(open(pathjoin(proj.projdir_path, proj.ballot_to_targets), 'rb'))

        self.somethingHasChanged = False

        #self.prefix = open(self.proj.classified+".prefix").read()
        
        self.parent = parent

        self.quarantined = []

        self.quarantined_targets = []
        
        self.visible_to_index = {}
        self.index_to_visible = {}

    def reset_panel(self):
        self.proj.removeCloseEvent(self.dosave)

    def setFilter(self):
        #gr = OverlayGrid(self, range(0,self.threshold), 
        #                 range(self.threshold,self.numberOfTargets))
        #gr.Show()
        #return

        dlg = wx.lib.dialogs.MultipleChoiceDialog(None, "Select the filter mode.", "Filter", ["Show All", "Show only even", "Show only filled", "Show only overvotes", "Show strange cases"]);
        dlg.ShowModal()

        self.jpgs = {}
        self.basejpgs = {}
        for each in self.images:
            self.images[each].Destroy()
        self.images = {}
        self.index_to_visible = {}
        self.visible_to_index = {}
        
        if dlg.GetValue()[0] == 0:
            self.visibleTargets = range(0,self.numberOfTargets)
        elif dlg.GetValue()[0] == 1:
            self.visibleTargets = range(0,self.numberOfTargets,2)
        elif dlg.GetValue()[0] == 2:
            self.visibleTargets = range(0,self.threshold)
        elif dlg.GetValue()[0] == 3:
            target_locs_map = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                        self.proj.target_locs_map), 'rb'))
            ballot_to_group = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                        self.proj.ballot_to_group), 'rb'))
            group_examples  = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                        self.proj.group_exmpls), 'rb'))

            has_contest_data = False
            if os.path.exists(self.proj.contest_text):
                has_contest_data = True
                contest_text = dict((x[0],x[1:]) for x in csv.reader(open(self.proj.contest_text, 'rb')))
                contest_id = dict((tuple(x[:2]),x[2:]) for x in csv.reader(open(self.proj.contest_id, 'rb')))
            over_count = {}
            self.visibleTargets = []
            for each in range(self.numberOfTargets):
                (bid, side, tid), _ = self.classified_file[each]
                targets = dict((x[4],x[5]) for y in target_locs_map[ballot_to_group[bid]][side] for x in y[1:])
                contest = targets[tid]
                if (bid,side,contest) not in over_count:
                    over_count[bid,side,contest] = []
                if (each < self.threshold) ^ (each in self.wrong):
                    #print 'there a target', each, bid, ballot_to_group[bid], tid, contest
                    over_count[bid,side,contest].append(each)
            for (bid,side,contest),targs in over_count.items():
                upto = 1
                if has_contest_data:
                    global_cid = contest_id[self.bal2imgs[group_examples[ballot_to_group[bid]][0]][side],str(contest)][0]
                    upto = int(contest_text[global_cid][0])
                if len(targs) > upto:
                    self.visibleTargets.extend(targs)
            self.visibleTargets = sorted(self.visibleTargets)
        elif dlg.GetValue()[0] == 4 or dlg.GetValue()[0] == 5:
            infile = open(self.proj.extractedfile)
            dims = map(int,open(self.proj.extractedfile+".size").read().strip()[1:-1].split(","))
            size = dims[0]*dims[1]
            counts = np.zeros((size,256),dtype=np.uint32)
            e = np.eye(size)
            while True:
                target = np.fromstring(infile.read(size), dtype='uint8')
                if len(target):
                    counts[np.arange(size),target] += 1
                else:
                    break
            
            sigmas = []
            for i in range(size):
                mu = np.sum(counts[i,:]*np.arange(256))/np.sum(counts[i,:])
                sigma = (np.sum(counts[i,:]*(np.arange(256)-mu)**2)/np.sum(counts[i,:]))**.5
                sigmas.append(sigma)
            print sigmas
            sigmas = np.array(sigmas)

            infile.seek(0)
            targets = []
            while True:
                target = np.fromstring(infile.read(size), dtype='uint8')
                if len(target):
                    targets.append(np.dot(target,sigmas))
                else:
                    break
            targets = np.array(targets)
            hist = np.bincount((((targets-np.min(targets))/(np.max(targets)-np.min(targets)))*256).astype(np.int32))
            print hist

            bound,_ = self.findBoundry(hist)
            argsorted = np.argsort(targets)
            weird = argsorted > self.threshold
            weird = list(np.arange(bound)[weird[:bound]])+list(np.arange(bound,len(weird))[np.logical_not(weird[bound:])])
            print weird
            print len(weird)
            self.visibleTargets = sorted(weird)
            

        self.numberOfVisibleTargets = len(self.visibleTargets)

        self.onScroll(self.lastpos)

    def getImageList(self):
        """
        Get a list of all the images.
        """

        target_locs_map = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                    self.proj.target_locs_map), 'rb'))
        
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
        self.basetargetw, self.basetargeth = w, h

        self.targetResize = 1

        self.changeSize(1, False)


    def findBoundry(self, usedata=None):
        if usedata == None:
            hist = [0]*256
            gaguge = MyGauge(self, 1)
            for _,v in self.classified_file:
                hist[v] += 1
        else:
            hist = usedata

        # I'm going to assume there are two normal dist. variables 
        #  which combine to make the histogram.


        # I'll go through all possible thresholds, and find the one which
        #  allows two normal dist. to match the best.

        def matchnormal(data):

            if sum(data) == 0: return 0
            if sum([1 if x != 0 else 0 for x in data]) == 1: return 0

            mean = float(sum([i*x for i,x in enumerate(data)]))/sum(data)
            total = sum(data)
            
            stdev = 0
            for i in range(len(data)):
                dist = abs(mean-i)
                sq = dist*dist
                stdev += sq*(float(data[i])/total)
            stdev = stdev**.5

            def pdf(m, s, x):
                return ((2*3.14*s*s)**-.5)*2.71**(-(x-m)**2/(2*s*s));

            err = 0
            for i in range(len(data)):
                err += abs((float(data[i])/total-pdf(mean,stdev,i)))
            return err

        best = None
        mval = 1<<30
        for line in range(1,255):
            lower = hist[:line]
            m1 = matchnormal(lower)
            upper = hist[line:]
            m2 = matchnormal(upper)
            if m1+m2 < mval:
                best = line
                mval = m1+m2
        print "BEST LINE", best

        count = sum(hist[:best])
        return count, (count-(self.numcols*self.numrows)/2)

    def changeSize(self, num, redraw=True):
        self.targetResize *= num

        self.targeth = int(self.basetargeth*self.targetResize)
        self.targetw = int(self.basetargetw*self.targetResize)

        self.numcols = int((self.parent.thesize[0]-30)/self.targetw)
        self.numrows = int(self.parent.thesize[1]/self.targeth)
        if redraw:
            self.setupScrollBars()

            startat = self.lastpos
            startat = startat - startat%self.numcols
            print "START AT ", startat
            print 'other', self.numcols, self.targeth

            self.onScroll(startat)

            if self.threshold != None:
                self.drawThreshold()
    
    def setupScrollBars(self):
        height = (self.numberOfTargets/self.numcols)*self.targeth

        print "Height", height
        self.SetScrollbars(1, 1, 1, int(height*1.05), 0, 0, True)
        self.Scroll(0, 0)
        self.Show(True)
        self.Centre()

        self.Layout()
        self.parent.Fit()
        self.Fit()

        for each in self.images:
            self.images[each].Destroy()

        self.jpgs = {}
        self.basejpgs = {}
        self.images = {}

    def setup(self):
        self.somethingHasChanged = True
        i = 0

        self.Bind(wx.EVT_SCROLLWIN_THUMBTRACK, 
                  lambda x: self.onScroll(evtpos=x.GetPosition()))
        self.Bind(wx.EVT_SCROLLWIN_THUMBRELEASE, 
                  lambda x: self.onScroll(evtpos=x.GetPosition()))
        self.Bind(wx.EVT_SCROLLWIN_LINEUP,
                  lambda x: self.onScroll(self.lastpos-self.numcols))
        self.Bind(wx.EVT_SCROLLWIN_LINEDOWN, 
                  lambda x: self.onScroll(self.lastpos+self.numcols))
        self.Bind(wx.EVT_SCROLLWIN_PAGEUP,
                  lambda x: self.onScroll(self.lastpos-self.numcols*self.numrows))
        self.Bind(wx.EVT_SCROLLWIN_PAGEDOWN, 
                  lambda x: self.onScroll(self.lastpos+self.numcols*self.numrows))


        self.classified_file = [l.split("\0") for l in open(self.proj.classified)]
        print self.classified_file[0]
        self.classified_file = [((int(bid),int(side),int(tid)),int(value)) for bid,side,tid,value in self.classified_file]
        self.classified_lookup = dict([(l, i) for i,(l,_) in enumerate(self.classified_file)])

        self.numberOfTargets = len(self.classified_file)
        self.visibleTargets = range(self.numberOfTargets)
        self.numberOfVisibleTargets = len(self.visibleTargets)


        """
        if os.path.exists(self.proj.classified+".index"):
            try:
                is64bit = (sys.maxsize > (2**32))
                size = 8 if is64bit else 4
                arr = array.array("L")
                arr.fromfile(open(self.proj.classified+".index"), 
                             os.path.getsize(self.proj.classified+".index")/size)
                self.classifiedindex = arr
            except Exception as e:
                print e
                print "Could not load index file. Doing it the slow way. err1"
                self.classifiedindex = None
        else:
            print "Could not load index file. Doing it the slow way. err2"
            self.classifiedindex = None
        """

        self.getImageList()

        self.imagefile = imageFile.ImageFile(self.proj.extractedfile)

        self.setupScrollBars()
        
        self.quarantined_targets = []
        if os.path.exists(self.proj.threshold_internal):
            dat = open(self.proj.threshold_internal).read()
            if dat:
                data = pickle.load(open(self.proj.threshold_internal))
                if len(data) == 4:
                    self.threshold, self.wrong, self.quarantined, self.quarantined_targets = data
                    self.onScroll(self.index_to_visible[self.threshold]-(self.numcols*self.numrows)/2)
                else:
                    self.threshold, self.wrong, self.quarantined, self.quarantined_targets, pos = data
                    self.onScroll(pos)

        else:
            newthresh, bound = self.findBoundry()
            self.onScroll(bound)
            self.setLine(newthresh)


    def clear_unused(self, low, high):
        #print "Del",
        keys = self.jpgs.keys()
        for each in keys:
            if low <= each <= high: continue
            #print each,
            del self.jpgs[each]
            del self.basejpgs[each]
            self.images[each].Destroy()
            del self.images[each]
        #print

    def onScroll(self, pos=None, evtpos=None):
        if evtpos != None:
            pos = int(evtpos/self.targeth*self.numcols)
        else:
            pos = pos - pos%self.numcols
        if pos < 0: pos = 0
        GAP = 0#self.numcols*4

        self.lastpos = pos
        low = max(0,pos-GAP)
        high = min(pos+self.numcols*self.numrows+GAP,self.numberOfVisibleTargets)

        self.clear_unused(low, high)

        qt = set(self.quarantined_targets)

        # Draw the images from low to high.
        for i in range(low,high,self.numcols):
            if i in self.jpgs:
                # If we've drawn it before, then it's still there, skip over it
                continue
            # Open and draw it.

            #jpg = self.imagefile.readManyImages(i, self.numcols, 
            #                                    self.basetargetw, self.basetargeth,
            #                                    self.targetw, self.targeth)
            todraw = self.visibleTargets[i:i+self.numcols]
            for realindex,onscreenindex in zip(todraw,range(i,i+len(todraw))):
                self.visible_to_index[onscreenindex] = realindex
                self.index_to_visible[realindex] = onscreenindex
            jpg = self.imagefile.readManyImages_filter(todraw, self.numcols, 
                                                self.basetargetw, self.basetargeth,
                                                self.targetw, self.targeth)

            # Want to be able to modify this but not the base
            self.jpgs[i] = jpg.copy()
            self.basejpgs[i] = jpg
            self.addimg(i)
            for j in range(self.numcols):
                if i+j in qt:
                    self.markQuarantine(i+j)

        ## Draw red mask over wrong targets
        idxs_wrong_todraw = []
        for each in self.wrong:
            if each in self.index_to_visible:
                if (self.index_to_visible[each]/self.numcols)*self.numcols in self.jpgs:
                    idxs_wrong_todraw.append(each)
        self.drawWrongMarks(idxs_wrong_todraw)

        if self.threshold != None and self.threshold in self.index_to_visible:
            if self.index_to_visible[self.threshold]/self.numcols*self.numcols in self.jpgs:
                self.drawThreshold()

        # Scroll us to the right place.
        if evtpos != None:
            self.Scroll(0, evtpos)
        else:
            self.Scroll(0, pos*self.targeth/self.numcols)
        # Record where we were last time.
        wx.CallAfter(self.Refresh)

    def dosave(self):
        """
        Export all results to disk. Writes the following files:

        1.) targets_result.csv
            A file containing a line for every target. Each line consists
            of the following:
                <BALLOTID>, <CONTESTID>, <TARGETID>, 0/1
            Where the last column is:
                '0' -- Filled
                '1' -- Empty
        2.) quarantined_manual.csv
            A file containing a line for every ballot quarantined during
            the SetThreshold panel. Each line is of the form:
                <BALLOTID_0>
                <BALLOTID_1>
                ...
        """
        if not self.somethingHasChanged: return
        self.somethingHasChanged = False

        print "SAVING!!!!"
        filled = {}
        unfilled = {}
        for i in range(self.numberOfTargets):
            if i not in self.wrong:
                if i < self.threshold:
                    filled[i] = True
                else:
                    unfilled[i] = True
            else:
                if i < self.threshold:
                    unfilled[i] = True
                else:
                    filled[i] = True
        f = open(self.proj.targets_result, "w")

        for i,(t,_) in enumerate(self.enumerateOverFullList()):
            if i in filled:
                f.write(", ".join(map(str,t))+", 1\n")
        for i,(t,_) in enumerate(self.enumerateOverFullList()):
            if i in unfilled:
                f.write(", ".join(map(str,t))+", 0\n")
        f.close()

        pickle.dump((self.threshold, self.wrong, self.quarantined, self.quarantined_targets, self.lastpos), open(self.proj.threshold_internal, "w"))
        img2bal = pickle.load(open(self.proj.image_to_ballot, 'rb'))
            
        out = open(self.proj.quarantined_manual, "w")
        for each in self.quarantined:
            if type(each) == type(0):
                targetpath = self.lookupFullList(each)[0]
                ballotpath = self.target_to_sample(targetpath)
                ballotid = img2bal[ballotpath]
                out.write(str(ballotid)+"\n")
            else:
                # EACH is ballotpath
                ballotid = img2bal[each]
                out.write(str(ballotid)+"\n")
        out.close()

class ThresholdPanel(wx.Panel):
    def __init__(self, parent, size):
        wx.Panel.__init__(self, parent, id=-1, size=size) 
        #print "AND SIZE", parent.GetSize()
        self.parent = parent

        self.tabOne = None

        self.parent.Fit()
    
    def reset_panel(self):
        self.tabOne.reset_panel()

    first = True
    def start(self, proj, size=None):
        self.proj = proj

        if not self.first: return
        self.first = False

        self.thesize = size

        sizer = wx.BoxSizer(wx.VERTICAL)

        tabOne = GridShow(self, self.proj)

        self.tabOne = tabOne

        top = wx.BoxSizer(wx.HORIZONTAL)
        button1 = wx.Button(self, label="Increase Size")
        button1.Bind(wx.EVT_BUTTON, lambda x: tabOne.changeSize(2))
        button2 = wx.Button(self, label="Decrease Size")
        button2.Bind(wx.EVT_BUTTON, lambda x: tabOne.changeSize(0.5))
        button3 = wx.Button(self, label="Scroll Up")
        button3.Bind(wx.EVT_BUTTON, lambda x: tabOne.onScroll(tabOne.lastpos-tabOne.numcols*(tabOne.numrows-5)))
        button4 = wx.Button(self, label="Scroll Down")
        button4.Bind(wx.EVT_BUTTON, lambda x: tabOne.onScroll(tabOne.lastpos+tabOne.numcols*(tabOne.numrows-5)))
        button5 = wx.Button(self, label="Set Filter")
        button5.Bind(wx.EVT_BUTTON, lambda x: tabOne.setFilter())

        button6 = wx.Button(self, label="(Dev) Jump To...")
        button6.Bind(wx.EVT_BUTTON, self.onButton_jumpto)
        button7 = wx.Button(self, label="(Dev) Print self.lastpos")
        button7.Bind(wx.EVT_BUTTON, self.onButton_printpos)
        if not config.IS_DEV:
            button6.Hide()
            button7.Hide()

        top.Add(button1)
        top.Add(button2)
        top.Add(button3)
        top.Add(button4)
        top.Add(button5)
        top.Add(button6)
        top.Add(button7)
        
        sizer.Add(top)
        tabOne.setup()
        self.Refresh()

        sizer.Add(tabOne, proportion=10, flag=wx.ALL|wx.EXPAND, border=5)

        self.SetSizer(sizer)
        self.Fit()
        self.Refresh()
        
    def stop(self):
        self.tabOne.dosave()

    def onButton_jumpto(self, evt):
        dlg = wx.TextEntryDialog(self, style=wx.CAPTION | wx.OK | wx.CANCEL,
                                 message="Please enter a position value greater than 0.")
        status = dlg.ShowModal()
        if status == wx.ID_CANCEL:
            return
        try:
            pos = int(dlg.GetValue())
            self.tabOne.onScroll(pos)
        except ValueError as e:
            print e
    def onButton_printpos(self, evt):
        print "self.tabOne.lastpos is:", self.tabOne.lastpos
