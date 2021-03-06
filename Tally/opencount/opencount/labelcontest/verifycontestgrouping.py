import wx
import sys
import os, pdb

sys.path.append("..")
from util import pdb_on_crash
import grouping.common
import pixel_reg.imagesAlign as imagesAlign
import pixel_reg.shared as sh
import numpy as np
import scipy.misc
import multiprocessing as mp

TMP = "tmp/"

def merge_and_align(dat):
    i, group = dat
    print i
    return [merge(align(i,group))]#[merge(align(i, group[x:x+10])) for x in range(0,len(group),100)]

def translate(name):
    return os.path.join(TMP,os.path.abspath(name).replace("/","~"))


@pdb_on_crash
def merge(args):
    all_files, all_images = args
    res = []
    for contest_paths,contest_images in zip(zip(*all_files),zip(*all_images)):
        name = os.path.commonprefix(contest_paths)+".png"
        M = np.zeros((sum(x.shape[0] for x in contest_images),
                      max(x.shape[1] for x in contest_images)))
        pos = 0
        for img in contest_images:
            M[pos:pos+img.shape[0],0:img.shape[1]] = img
            pos += img.shape[0]
        scipy.misc.imsave(name, M)
        res.append(name)
    return res

def make_norm(I, Iref):
    Inorm = np.zeros(Iref.shape, dtype=Iref.dtype)
    # make patch the same size as Iref
        
    min0 = min(I.shape[0],Iref.shape[0])
    min1 = min(I.shape[1],Iref.shape[1])
    Inorm[0:min0,0:min1] = I[0:min0,0:min1]
        
    diff0 = Iref.shape[0] - I.shape[0]
    diff1 = Iref.shape[1] - I.shape[1]
        
    if diff0 > 0:
        Inorm[I.shape[0]:I.shape[0]+diff0,:] = 1
    if diff1 > 0:
        Inorm[:,I.shape[1]:I.shape[1]+diff1] = 1

    return Inorm

@pdb_on_crash
def align(groupid, dat):
    res = []
    translations = []
    
    for i,group in enumerate(zip(*dat)):

        if i == 0:
            # We want to look at everything for the title
            left_border = 0
        else:
            # Skip the voting target for the rest
            #left_border = 80
            left_border = 0
        
        Iref_orig=sh.standardImread(group[0],flatten=True)
        Iref = Iref_orig[:,left_border:]
        r = []
        r_img = []
    
        for i in range(len(group)):
            I_orig=sh.standardImread(group[i],flatten=True)
            I=I_orig[:,left_border:]
            Inorm = make_norm(I, Iref)
            
            (H,imres,err)=imagesAlign.imagesAlign(Inorm,Iref,trfm_type='translation')

            r_img.append((make_norm(I_orig, Iref_orig), H))
            r.append(translate(group[i]))

        translations.append(r_img)
        res.append(r)

    translated_images = []
    for contest in zip(*translations):
        c_res = []
        """
        print 'new'
        arr = np.zeros((3,3))
        for _,H in contest:
            arr += H
        arr /= len(contest)
        print arr
        """
        for img,H in contest:
            translated = sh.imtransform(np.copy(img), H, fillval=np.nan)
            align_res = np.nan_to_num(translated)
            c_res.append(align_res)
        translated_images.append(c_res)
    translated_images = zip(*translated_images)

    return res, translated_images


class VerifyContestGrouping:
    def __init__(self, ocrdir, dirList, equivs, reorder, reorder_inverse, mapping, mapping_inverse, multiboxcontests, callback, NPROC=None):
        #print "ARGS", (ocrdir, dirList, equivs, reorder, reorder_inverse, mapping, mapping_inverse, multiboxcontests)
        global TMP
        self.callback = callback
        TMP = ocrdir

        self.ocrdir = ocrdir
        self.dirList = dirList
        self.equivs = equivs
        self.reorder = reorder
        self.reorder_inverse = reorder_inverse
        self.mapping = mapping
        self.mapping_inverse = mapping_inverse
        self.multiboxcontests = multiboxcontests
        self.processgroups = [i for i,x in enumerate(self.equivs) if len(x) > 1]

        #print self.equivs
        #print self.processgroups
        res = []
        if NPROC == None:
            NPROC = mp.cpu_count()
        print "(Info) Using {0} processes for merge_and_align".format(NPROC)
        if NPROC == 1:
            res = []
            args = enumerate(map(self.generate_one, range(len(self.processgroups))))
            for arg in args:
                res.append(merge_and_align(arg))
                
        else:
            pool = mp.Pool(mp.cpu_count())
            print "Go up to", len(self.processgroups)
            res = pool.map(merge_and_align, enumerate(map(self.generate_one, range(len(self.processgroups)))))
        res = [x for y in res for x in y]
        #print len(res), map(len,res)
        
        # TODO: Provide the 'realign_callback' function for realigning a
        # set of overlay'd contest patches. See the docstring for 
        #     verify_overlays_new.SeparateImages.do_realign
        realign_callback = None
        frame = grouping.verify_overlays_new.SeparateImagesFrame(None, res, self.on_verify_done,
                                                                 realign_callback=realign_callback)
        frame.Maximize()
        frame.Show()

    @pdb_on_crash
    def on_verify_done(self, results):
        """ Called when user finishes verifying the grouping.
        Input:
            list results: List of lists, where each sublist is considered
                one 'group': [[imgpath_0i, ...], [imgpath_1i, ...], ...]
        """
        mapping = {}
        for i,group in enumerate(results):
            for j,path in enumerate(group):
                print path
                mapping[path] = i
        sets = {}
        for groupid in self.processgroups:
            group = self.equivs[groupid]
            print "NEXT GROUP"
            for ballot, contest in group:
                print "NEW", ballot, contest
                print self.get_files(ballot, contest)
                print self.translate(os.path.commonprefix(self.get_files(ballot, contest)))+"~.png"
                ids = mapping[self.translate(os.path.commonprefix(map(os.path.abspath,self.get_files(ballot, contest))))+"~.png"]
                print ids
                
                if ids not in sets: sets[ids] = []
                sets[ids].append((ballot, contest))
            print
        print sets
        self.callback(sets.values())
        
    @pdb_on_crash
    def get_files(self, ballot, contest):
        ballotname = os.path.split(self.dirList[ballot])[1].split('.')[0]
        boundingbox = (ballot, contest)
        if any(boundingbox in x for x in self.multiboxcontests):
            boundingboxes = [x for x in self.multiboxcontests if boundingbox in x][0]
            boundingbox = [x for x in boundingboxes if x in self.mapping_inverse][0]
            boundingboxes = [k[1] for k,v in self.mapping.items() if v == boundingbox]
        else:
            boundingboxes = [self.mapping_inverse[boundingbox][1]]
            
        boundingboxes = sorted(boundingboxes)

        ballotdir = os.path.join(self.ocrdir,ballotname+"-dir")
        boundingboxdirs = [os.path.join(ballotdir, '-'.join(map(str,bb))) for bb in boundingboxes]
        order = dict(self.reorder[self.reorder_inverse[ballot,contest]][ballot,contest])
        images = [[img for img in os.listdir(bbdir) if img[-3:] != 'txt'] for bbdir in boundingboxdirs]

        images = [sorted(imgs, key=lambda x: int(x.split('.')[0])) for imgs in images]
        title = images[0][0]
        images = [(i,y) for i,x in enumerate(images) for y in x[1:]]
        orderedimages = [None]*(len(images)+1)
        orderedimages[0] = (0, title)
        for i in range(len(images)):
            orderedimages[i+1] = images[order[i]]
        paths = [os.path.join(boundingboxdirs[i],img) for i,img in orderedimages]
        return paths

    def generate_one(self, which):
        orderedpaths = []
        #print "STARTING", self.equivs[self.processgroups[which]]
        for ballot,contest in self.equivs[self.processgroups[which]]:
            orderedpaths.append((self.get_files(ballot, contest)))
        return orderedpaths

    def translate(self, name):
        return os.path.join(TMP,os.path.abspath(name).replace("/","~"))
            
            

if __name__ == '__main__':
    app = wx.App(False)
    VerifyContestGrouping(u'../projects_new/better/ocr_tmp_dir', [u'/home/nicholas/opencount/test-ballots/small_orange/339_100/339_1000_4_173_1.png', u'/home/nicholas/opencount/test-ballots/small_orange/339_100/339_1001_4_172_2.png', u'/home/nicholas/opencount/test-ballots/small_orange/339_100/339_1000_4_174_2.png', u'/home/nicholas/opencount/test-ballots/small_orange/339_100/339_1003_4_168_2.png', u'/home/nicholas/opencount/test-ballots/small_orange/339_100/339_1007_4_159_1.png', u'/home/nicholas/opencount/test-ballots/small_orange/339_100/339_1004_4_165_1.png', u'/home/nicholas/opencount/test-ballots/small_orange/339_100/339_1009_4_155_1.png', u'/home/nicholas/opencount/test-ballots/small_orange/339_100/339_1003_4_167_1.png', u'/home/nicholas/opencount/test-ballots/small_orange/339_100/339_1006_4_162_2.png', u'/home/nicholas/opencount/test-ballots/small_orange/339_100/339_1008_4_157_1.png', u'/home/nicholas/opencount/test-ballots/small_orange/339_100/339_1007_4_160_2.png', u'/home/nicholas/opencount/test-ballots/small_orange/339_100/339_1006_4_161_1.png', u'/home/nicholas/opencount/test-ballots/small_orange/339_100/339_1005_4_164_2.png', u'/home/nicholas/opencount/test-ballots/small_orange/339_100/339_1002_4_169_1.png', u'/home/nicholas/opencount/test-ballots/small_orange/339_100/339_1001_4_171_1.png', u'/home/nicholas/opencount/test-ballots/small_orange/339_100/339_1009_4_156_2.png', u'/home/nicholas/opencount/test-ballots/small_orange/339_100/339_1005_4_163_1.png', u'/home/nicholas/opencount/test-ballots/small_orange/339_100/339_1008_4_158_2.png', u'/home/nicholas/opencount/test-ballots/small_orange/339_100/339_1004_4_166_2.png', u'/home/nicholas/opencount/test-ballots/small_orange/339_100/339_1002_4_170_2.png'], [[(18, 0), (15, 0)], [(2, 0)], [(1, 0)], [(17, 0)], [(3, 0)], [(10, 0)], [(19, 0)], [(12, 0)], [(8, 0)], [(1, 2)], [(10, 1)], [(2, 2)], [(19, 2)], [(8, 1)], [(18, 1)], [(3, 1)], [(12, 2)], [(17, 1)], [(15, 2)], [(18, 2)], [(17, 2)], [(10, 2)], [(1, 1)], [(8, 2)], [(19, 1)], [(12, 1)], [(3, 2)], [(15, 1)], [(2, 1)], [(12, 4)], [(8, 4)], [(12, 3)], [(8, 3)], [(15, 3)], [(17, 3)], [(18, 3)], [(15, 4)], [(17, 4)], [(1, 3)], [(2, 3)], [(3, 3)], [(19, 3)], [(10, 3)], [(12, 5)], [(8, 5)], [(8, 7)], [(18, 5)], [(15, 6)], [(15, 11)], [(17, 9)], [(1, 4)], [(12, 6), (10, 4), (8, 6), (17, 7), (19, 4)], [(18, 4)], [(2, 5)], [(2, 4)], [(15, 5)], [(17, 5)], [(3, 4)], [(10, 6)], [(18, 6)], [(19, 5)], [(15, 8)], [(15, 7), (18, 7)], [(3, 5)], [(8, 8)], [(10, 5), (17, 6)], [(15, 10), (1, 5), (18, 9)], [(17, 8), (10, 8)], [(1, 6)], [(12, 7)], [(18, 8)], [(15, 9)], [(10, 7)], [(8, 9)], [(12, 8)], [(17, 10)], [(11, 0)], [(4, 0)], [(13, 0)], [(0, 0)], [(14, 0), (16, 0)], [(6, 0)], [(7, 0)], [(5, 0), (9, 0)], [(4, 1), (5, 1)], [(13, 1)], [(14, 1)], [(9, 1)], [(6, 1)], [(7, 1)], [(19, 6)], [(3, 6)], [(2, 6)], [(2, 7)], [(12, 9)], [(8, 10)], [(2, 8)], [(16, 1)], [(0, 1)], [(5, 2)], [(11, 1)], [(13, 2)], [(7, 2)], [(4, 2)], [(14, 2)], [(9, 2)], [(6, 2)], [(5, 3)], [(7, 3)], [(4, 3)], [(13, 3)], [(14, 3)], [(9, 3)], [(16, 2)], [(6, 3)], [(11, 2)], [(0, 2)]], {(7, 3): {(7, 3): [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14)]}, (12, 1): {(12, 1): [(0, 0), (1, 1)]}, (18, 4): {(18, 4): [(0, 0), (1, 1), (2, 2)]}, (15, 1): {(15, 1): [(0, 0), (1, 1)]}, (1, 6): {(1, 6): [(0, 0), (1, 1), (2, 2)]}, (2, 5): {(2, 5): [(0, 0), (1, 1), (2, 2)]}, (8, 5): {(8, 5): [(0, 0), (1, 1)]}, (4, 0): {(4, 0): [(0, 0), (1, 1), (2, 2), (3, 3)]}, (10, 7): {(10, 7): [(0, 0), (1, 1), (2, 2)]}, (12, 6): {(8, 6): [(0, 0), (1, 1), (2, 2)], (17, 7): [(0, 1), (1, 0), (2, 2)], (19, 4): [(0, 1), (1, 0), (2, 2)], (12, 6): [(0, 0), (1, 1), (2, 2)], (10, 4): [(0, 1), (1, 0), (2, 2)]}, (17, 2): {(17, 2): [(0, 0), (1, 1)]}, (15, 11): {(15, 11): [(0, 0), (1, 1)]}, (14, 1): {(14, 1): [(0, 0), (1, 1), (2, 2), (3, 3)]}, (19, 3): {(19, 3): [(0, 0), (1, 1)]}, (15, 4): {(15, 4): [(0, 0), (1, 1)]}, (1, 1): {(1, 1): [(0, 0), (1, 1)]}, (3, 2): {(3, 2): [(0, 0), (1, 1)]}, (2, 6): {(2, 6): [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4)]}, (8, 2): {(8, 2): [(0, 0), (1, 1)]}, (9, 3): {(9, 3): [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14)]}, (6, 0): {(6, 0): [(0, 0), (1, 1), (2, 2), (3, 3)]}, (11, 0): {(11, 0): [(0, 0), (1, 1), (2, 2), (3, 3)]}, (14, 2): {(14, 2): [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9)]}, (0, 1): {(0, 1): [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9)]}, (3, 1): {(3, 1): [(0, 0), (1, 1)]}, (13, 0): {(13, 0): [(0, 0), (1, 1), (2, 2), (3, 3)]}, (12, 8): {(12, 8): [(0, 0), (1, 1), (2, 2)]}, (18, 0): {(18, 0): [(0, 0), (1, 1)], (15, 0): [(0, 0), (1, 1)]}, (17, 8): {(10, 8): [(0, 0), (1, 1), (2, 2)], (17, 8): [(0, 0), (1, 1), (2, 2)]}, (2, 1): {(2, 1): [(0, 0), (1, 1)]}, (8, 9): {(8, 9): [(0, 0), (1, 1), (2, 2)]}, (10, 3): {(10, 3): [(0, 0), (1, 1)]}, (7, 2): {(7, 2): [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9)]}, (12, 2): {(12, 2): [(0, 0), (1, 1)]}, (13, 3): {(13, 3): [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14)]}, (18, 5): {(18, 5): [(0, 0), (1, 1)]}, (3, 6): {(3, 6): [(0, 0), (1, 1), (2, 2), (3, 3)]}, (2, 2): {(2, 2): [(0, 0), (1, 1)]}, (4, 1): {(5, 1): [(0, 0), (1, 1), (2, 2), (3, 3)], (4, 1): [(0, 0), (1, 1), (2, 2), (3, 3)]}, (7, 1): {(7, 1): [(0, 0), (1, 1), (2, 2), (3, 3)]}, (12, 7): {(12, 7): [(0, 0), (1, 1), (2, 2)]}, (17, 1): {(17, 1): [(0, 0), (1, 1)]}, (15, 10): {(1, 5): [(0, 0), (1, 1), (2, 2)], (18, 9): [(0, 0), (1, 1), (2, 2)], (15, 10): [(0, 0), (1, 1), (2, 2)]}, (19, 2): {(19, 2): [(0, 0), (1, 1)]}, (18, 6): {(18, 6): [(0, 0), (1, 1), (2, 2)]}, (15, 7): {(18, 7): [(0, 0), (1, 1), (2, 2)], (15, 7): [(0, 0), (1, 1), (2, 2)]}, (1, 0): {(1, 0): [(0, 0), (1, 1)]}, (3, 5): {(3, 5): [(0, 0), (1, 1), (2, 2)]}, (2, 7): {(2, 7): [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5)]}, (8, 3): {(8, 3): [(0, 0), (1, 1)]}, (9, 2): {(9, 2): [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9)]}, (6, 1): {(6, 1): [(0, 0), (1, 1), (2, 2), (3, 3)]}, (16, 1): {(16, 1): [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9)]}, (12, 4): {(12, 4): [(0, 0), (1, 1)]}, (15, 9): {(15, 9): [(0, 0), (1, 1), (2, 2)]}, (14, 3): {(14, 3): [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14)]}, (19, 1): {(19, 1): [(0, 0), (1, 1)]}, (0, 2): {(0, 2): [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14)]}, (1, 3): {(1, 3): [(0, 0), (1, 1)]}, (3, 0): {(3, 0): [(0, 0), (1, 1)]}, (2, 8): {(2, 8): [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8)]}, (8, 0): {(8, 0): [(0, 0), (1, 1)]}, (6, 2): {(6, 2): [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9)]}, (12, 9): {(12, 9): [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8)]}, (18, 1): {(18, 1): [(0, 0), (1, 1)]}, (8, 10): {(8, 10): [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8)]}, (5, 0): {(9, 0): [(0, 0), (1, 1), (2, 2), (3, 3)], (5, 0): [(0, 0), (1, 1), (2, 2), (3, 3)]}, (10, 0): {(10, 0): [(0, 0), (1, 1)]}, (12, 3): {(12, 3): [(0, 0), (1, 1)]}, (17, 5): {(17, 5): [(0, 0), (1, 1), (2, 2)]}, (13, 2): {(13, 2): [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9)]}, (19, 6): {(19, 6): [(0, 0), (1, 1), (2, 2), (3, 3)]}, (18, 2): {(18, 2): [(0, 0), (1, 1)]}, (17, 10): {(17, 10): [(0, 0), (1, 1), (2, 2)]}, (15, 3): {(15, 3): [(0, 0), (1, 1)]}, (1, 4): {(1, 4): [(0, 0), (1, 1), (2, 2)]}, (2, 3): {(2, 3): [(0, 0), (1, 1)]}, (8, 7): {(8, 7): [(0, 0), (1, 1)]}, (4, 2): {(4, 2): [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9)]}, (5, 3): {(5, 3): [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14)]}, (10, 5): {(10, 5): [(0, 0), (1, 1), (2, 2)], (17, 6): [(0, 0), (1, 1), (2, 2)]}, (7, 0): {(7, 0): [(0, 0), (1, 1), (2, 2), (3, 3)]}, (12, 0): {(12, 0): [(0, 0), (1, 1)]}, (17, 0): {(17, 0): [(0, 0), (1, 1)]}, (19, 5): {(19, 5): [(0, 0), (1, 1), (2, 2)]}, (15, 6): {(15, 6): [(0, 0), (1, 1)]}, (3, 4): {(3, 4): [(0, 0), (1, 1), (2, 2)]}, (2, 4): {(2, 4): [(0, 0), (1, 1), (2, 2)]}, (8, 4): {(8, 4): [(0, 0), (1, 1)]}, (9, 1): {(9, 1): [(0, 0), (1, 1), (2, 2), (3, 3)]}, (11, 2): {(11, 2): [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14)]}, (10, 6): {(10, 6): [(0, 0), (1, 1), (2, 2)]}, (16, 2): {(16, 2): [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14)]}, (12, 5): {(12, 5): [(0, 0), (1, 1)]}, (17, 3): {(17, 3): [(0, 0), (1, 1)]}, (15, 8): {(15, 8): [(0, 0), (1, 1), (2, 2)]}, (14, 0): {(16, 0): [(0, 2), (1, 0), (2, 1), (3, 3)], (14, 0): [(0, 0), (1, 1), (2, 2), (3, 3)]}, (19, 0): {(19, 0): [(0, 0), (1, 1)]}, (18, 8): {(18, 8): [(0, 0), (1, 1), (2, 2)]}, (15, 5): {(15, 5): [(0, 0), (1, 1), (2, 2)]}, (1, 2): {(1, 2): [(0, 0), (1, 1)]}, (3, 3): {(3, 3): [(0, 0), (1, 1)]}, (8, 1): {(8, 1): [(0, 0), (1, 1)]}, (6, 3): {(6, 3): [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14)]}, (11, 1): {(11, 1): [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9)]}, (0, 0): {(0, 0): [(0, 0), (1, 1), (2, 2), (3, 3)]}, (10, 1): {(10, 1): [(0, 0), (1, 1)]}, (17, 4): {(17, 4): [(0, 0), (1, 1)]}, (13, 1): {(13, 1): [(0, 0), (1, 1), (2, 2), (3, 3)]}, (18, 3): {(18, 3): [(0, 0), (1, 1)]}, (17, 9): {(17, 9): [(0, 0), (1, 1)]}, (15, 2): {(15, 2): [(0, 0), (1, 1)]}, (2, 0): {(2, 0): [(0, 0), (1, 1)]}, (8, 8): {(8, 8): [(0, 0), (1, 1), (2, 2)]}, (4, 3): {(4, 3): [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14)]}, (5, 2): {(5, 2): [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9)]}, (10, 2): {(10, 2): [(0, 0), (1, 1)]}}, {(7, 3): (7, 3), (12, 1): (12, 1), (17, 7): (12, 6), (19, 4): (12, 6), (18, 4): (18, 4), (15, 1): (15, 1), (1, 6): (1, 6), (2, 5): (2, 5), (8, 5): (8, 5), (4, 0): (4, 0), (10, 8): (17, 8), (9, 0): (5, 0), (10, 7): (10, 7), (12, 6): (12, 6), (17, 2): (17, 2), (15, 11): (15, 11), (14, 1): (14, 1), (19, 3): (19, 3), (18, 9): (15, 10), (15, 4): (15, 4), (1, 1): (1, 1), (3, 2): (3, 2), (2, 6): (2, 6), (8, 2): (8, 2), (9, 3): (9, 3), (6, 0): (6, 0), (11, 0): (11, 0), (16, 0): (14, 0), (14, 2): (14, 2), (0, 1): (0, 1), (3, 1): (3, 1), (13, 0): (13, 0), (12, 8): (12, 8), (18, 0): (18, 0), (17, 8): (17, 8), (2, 1): (2, 1), (8, 9): (8, 9), (5, 1): (4, 1), (10, 3): (10, 3), (7, 2): (7, 2), (12, 2): (12, 2), (17, 6): (10, 5), (13, 3): (13, 3), (18, 5): (18, 5), (15, 0): (18, 0), (1, 5): (15, 10), (3, 6): (3, 6), (2, 2): (2, 2), (8, 6): (12, 6), (4, 1): (4, 1), (10, 4): (12, 6), (7, 1): (7, 1), (12, 7): (12, 7), (17, 1): (17, 1), (15, 10): (15, 10), (19, 2): (19, 2), (18, 6): (18, 6), (15, 7): (15, 7), (1, 0): (1, 0), (3, 5): (3, 5), (2, 7): (2, 7), (8, 3): (8, 3), (9, 2): (9, 2), (6, 1): (6, 1), (16, 1): (16, 1), (12, 4): (12, 4), (15, 9): (15, 9), (14, 3): (14, 3), (19, 1): (19, 1), (0, 2): (0, 2), (1, 3): (1, 3), (3, 0): (3, 0), (2, 8): (2, 8), (8, 0): (8, 0), (6, 2): (6, 2), (12, 9): (12, 9), (18, 1): (18, 1), (8, 10): (8, 10), (5, 0): (5, 0), (10, 0): (10, 0), (12, 3): (12, 3), (17, 5): (17, 5), (13, 2): (13, 2), (19, 6): (19, 6), (18, 2): (18, 2), (17, 10): (17, 10), (15, 3): (15, 3), (1, 4): (1, 4), (2, 3): (2, 3), (8, 7): (8, 7), (4, 2): (4, 2), (5, 3): (5, 3), (10, 5): (10, 5), (7, 0): (7, 0), (12, 0): (12, 0), (17, 0): (17, 0), (19, 5): (19, 5), (18, 7): (15, 7), (15, 6): (15, 6), (3, 4): (3, 4), (2, 4): (2, 4), (8, 4): (8, 4), (9, 1): (9, 1), (11, 2): (11, 2), (10, 6): (10, 6), (16, 2): (16, 2), (12, 5): (12, 5), (17, 3): (17, 3), (15, 8): (15, 8), (14, 0): (14, 0), (19, 0): (19, 0), (18, 8): (18, 8), (15, 5): (15, 5), (1, 2): (1, 2), (3, 3): (3, 3), (8, 1): (8, 1), (6, 3): (6, 3), (11, 1): (11, 1), (0, 0): (0, 0), (10, 1): (10, 1), (17, 4): (17, 4), (13, 1): (13, 1), (18, 3): (18, 3), (17, 9): (17, 9), (15, 2): (15, 2), (2, 0): (2, 0), (8, 8): (8, 8), (4, 3): (4, 3), (5, 2): (5, 2), (10, 2): (10, 2)}, {(8, (1107, 1093, 1598, 1431)): (8, 4), (17, (618, 2050, 1104, 2415)): (17, 3), (18, (615, 1100, 1107, 1496)): (18, 3), (16, (1099, 327, 1601, 1727)): (16, 1), (12, (608, 1801, 1106, 2198)): (12, 5), (2, (1101, 1784, 1603, 2056)): (2, 2), (1, (606, 962, 1103, 1232)): (1, 2), (9, (1100, 313, 1603, 1728)): (9, 2), (13, (126, 1014, 618, 1428)): (13, 0), (3, (121, 807, 615, 1444)): (3, 6), (2, (1101, 881, 1603, 1151)): (2, 1), (11, (1101, 321, 1604, 1728)): (11, 1), (2, (1101, 1581, 1603, 1790)): (2, 0), (19, (121, 1650, 612, 2080)): (19, 4), (9, (609, 313, 1106, 2575)): (9, 3), (17, (129, 1509, 614, 1945)): (17, 7), (18, (615, 834, 1107, 1106)): (18, 2), (18, (615, 1534, 1107, 1745)): (18, 0), (15, (605, 1095, 1106, 1495)): (15, 4), (8, (618, 1020, 1104, 1450)): (8, 6), (17, (129, 809, 614, 1302)): (17, 10), (18, (126, 1509, 612, 1941)): (18, 4), (12, (608, 2236, 1106, 2448)): (12, 0), (8, (1107, 629, 1598, 1055)): (8, 7), (5, (609, 327, 1106, 2573)): (5, 3), (10, (125, 1507, 617, 1936)): (10, 4), (0, (610, 317, 1107, 2576)): (0, 2), (1, (119, 1509, 612, 1937)): (1, 4), (17, (618, 327, 1104, 751)): (17, 5), (3, (121, 315, 615, 813)): (3, 5), (12, (119, 1671, 614, 2165)): (12, 7), (18, (126, 321, 612, 811)): (18, 9), (13, (1101, 1725, 1604, 2358)): (13, 1), (11, (610, 321, 1107, 2570)): (11, 2), (17, (129, 1979, 614, 2407)): (17, 6), (7, (122, 1012, 615, 1423)): (7, 0), (9, (1100, 1722, 1603, 2358)): (9, 1), (3, (609, 958, 1107, 1230)): (3, 1), (15, (118, 813, 611, 1300)): (15, 9), (8, (129, 1673, 613, 2163)): (8, 8), (10, (611, 317, 1108, 751)): (10, 6), (12, (119, 311, 614, 1677)): (12, 9), (10, (611, 1737, 1108, 2008)): (10, 1), (4, (123, 1013, 617, 1424)): (4, 0), (6, (613, 321, 1107, 2568)): (6, 3), (13, (1101, 315, 1604, 1731)): (13, 2), (14, (606, 318, 1105, 2574)): (14, 3), (8, (1107, 1423, 1598, 1755)): (8, 3), (1, (119, 322, 612, 813)): (1, 5), (17, (618, 1536, 1104, 1746)): (17, 0), (15, (118, 1508, 611, 1940)): (15, 5), (15, (605, 2050, 1106, 2477)): (15, 6), (1, (606, 322, 1103, 717)): (1, 3), (10, (611, 1535, 1108, 1743)): (10, 0), (15, (605, 318, 1106, 749)): (15, 8), (15, (605, 833, 1106, 1105)): (15, 1), (8, (618, 324, 1104, 812)): (8, 9), (11, (124, 1013, 616, 1424)): (11, 0), (6, (1101, 321, 1603, 1724)): (6, 2), (19, (121, 314, 612, 810)): (19, 5), (2, (610, 1452, 1107, 1884)): (2, 4), (19, (121, 804, 612, 1442)): (19, 6), (14, (119, 1010, 612, 1423)): (14, 0), (17, (618, 1103, 1104, 1496)): (17, 4), (12, (608, 311, 1106, 808)): (12, 8), (17, (129, 327, 614, 815)): (17, 8), (1, (606, 755, 1103, 968)): (1, 0), (15, (118, 318, 611, 809)): (15, 10), (12, (608, 1018, 1106, 1448)): (12, 6), (17, (1107, 327, 1599, 809)): (17, 9), (15, (118, 1979, 611, 2415)): (15, 7), (18, (615, 1739, 1107, 2011)): (18, 1), (13, (612, 315, 1107, 2577)): (13, 3), (2, (123, 318, 616, 1678)): (2, 8), (5, (1100, 327, 1602, 1727)): (5, 2), (10, (611, 1099, 1108, 1495)): (10, 3), (8, (618, 1534, 1104, 1805)): (8, 2), (0, (123, 1012, 616, 1425)): (0, 0), (7, (1100, 1719, 1601, 2353)): (7, 1), (17, (618, 1740, 1104, 2012)): (17, 1), (7, (609, 324, 1106, 2571)): (7, 3), (18, (615, 321, 1107, 749)): (18, 6), (3, (609, 315, 1107, 715)): (3, 3), (5, (123, 1011, 615, 1424)): (5, 0), (1, (119, 807, 612, 1300)): (1, 6), (3, (121, 2167, 615, 2442)): (3, 2), (12, (1100, 311, 1602, 588)): (12, 2), (12, (1100, 953, 1602, 1289)): (12, 4), (2, (610, 1923, 1107, 2578)): (2, 6), (18, (126, 1978, 612, 2413)): (18, 7), (3, (609, 755, 1107, 964)): (3, 0), (10, (611, 833, 1108, 1105)): (10, 2), (10, (125, 317, 617, 812)): (10, 8), (15, (1100, 318, 1602, 683)): (15, 3), (19, (606, 753, 1102, 962)): (19, 0), (5, (1100, 1721, 1602, 2356)): (5, 1), (17, (618, 836, 1104, 1109)): (17, 2), (7, (1100, 324, 1601, 1725)): (7, 2), (4, (1101, 330, 1602, 1727)): (4, 2), (15, (1100, 677, 1602, 1166)): (15, 11), (19, (606, 314, 1102, 714)): (19, 3), (8, (129, 324, 613, 1679)): (8, 10), (1, (119, 2028, 612, 2290)): (1, 1), (18, (126, 816, 612, 1302)): (18, 8), (19, (606, 956, 1102, 1229)): (19, 2), (6, (1101, 1718, 1603, 2351)): (6, 1), (8, (618, 1799, 1104, 2195)): (8, 5), (14, (1099, 318, 1602, 1728)): (14, 2), (18, (615, 2049, 1107, 2477)): (18, 5), (2, (610, 318, 1107, 1247)): (2, 7), (16, (126, 1014, 616, 1426)): (16, 0), (0, (1101, 317, 1602, 1730)): (0, 1), (8, (1107, 324, 1598, 590)): (8, 1), (15, (605, 1739, 1106, 2012)): (15, 2), (3, (121, 1652, 615, 2083)): (3, 4), (12, (608, 1533, 1106, 1807)): (12, 1), (15, (605, 1534, 1106, 1745)): (15, 0), (16, (610, 327, 1105, 2572)): (16, 2), (4, (611, 330, 1107, 2571)): (4, 3), (4, (1101, 1721, 1602, 2355)): (4, 1), (12, (1100, 626, 1602, 959)): (12, 3), (14, (1099, 1722, 1602, 2357)): (14, 1), (10, (125, 806, 617, 1299)): (10, 7), (6, (127, 1011, 619, 1424)): (6, 0), (2, (1101, 365, 1603, 797)): (2, 5), (8, (618, 2233, 1104, 2443)): (8, 0), (9, (124, 1013, 615, 1427)): (9, 0), (10, (125, 1975, 617, 2409)): (10, 5), (19, (121, 2164, 612, 2436)): (19, 1), (2, (1101, 1145, 1603, 1542)): (2, 3)}, {(7, 3): (7, (609, 324, 1106, 2571)), (12, 1): (12, (608, 1533, 1106, 1807)), (17, 7): (17, (129, 1509, 614, 1945)), (19, 4): (19, (121, 1650, 612, 2080)), (18, 4): (18, (126, 1509, 612, 1941)), (15, 1): (15, (605, 833, 1106, 1105)), (1, 6): (1, (119, 807, 612, 1300)), (2, 5): (2, (1101, 365, 1603, 797)), (8, 5): (8, (618, 1799, 1104, 2195)), (4, 0): (4, (123, 1013, 617, 1424)), (10, 8): (10, (125, 317, 617, 812)), (9, 0): (9, (124, 1013, 615, 1427)), (10, 7): (10, (125, 806, 617, 1299)), (12, 6): (12, (608, 1018, 1106, 1448)), (17, 2): (17, (618, 836, 1104, 1109)), (15, 11): (15, (1100, 677, 1602, 1166)), (14, 1): (14, (1099, 1722, 1602, 2357)), (19, 3): (19, (606, 314, 1102, 714)), (18, 9): (18, (126, 321, 612, 811)), (15, 4): (15, (605, 1095, 1106, 1495)), (1, 1): (1, (119, 2028, 612, 2290)), (3, 2): (3, (121, 2167, 615, 2442)), (2, 6): (2, (610, 1923, 1107, 2578)), (8, 2): (8, (618, 1534, 1104, 1805)), (9, 3): (9, (609, 313, 1106, 2575)), (6, 0): (6, (127, 1011, 619, 1424)), (11, 0): (11, (124, 1013, 616, 1424)), (16, 0): (16, (126, 1014, 616, 1426)), (14, 2): (14, (1099, 318, 1602, 1728)), (0, 1): (0, (1101, 317, 1602, 1730)), (3, 1): (3, (609, 958, 1107, 1230)), (13, 0): (13, (126, 1014, 618, 1428)), (12, 8): (12, (608, 311, 1106, 808)), (18, 0): (18, (615, 1534, 1107, 1745)), (17, 8): (17, (129, 327, 614, 815)), (2, 1): (2, (1101, 881, 1603, 1151)), (8, 9): (8, (618, 324, 1104, 812)), (5, 1): (5, (1100, 1721, 1602, 2356)), (10, 3): (10, (611, 1099, 1108, 1495)), (7, 2): (7, (1100, 324, 1601, 1725)), (12, 2): (12, (1100, 311, 1602, 588)), (17, 6): (17, (129, 1979, 614, 2407)), (13, 3): (13, (612, 315, 1107, 2577)), (18, 5): (18, (615, 2049, 1107, 2477)), (15, 0): (15, (605, 1534, 1106, 1745)), (1, 5): (1, (119, 322, 612, 813)), (3, 6): (3, (121, 807, 615, 1444)), (2, 2): (2, (1101, 1784, 1603, 2056)), (8, 6): (8, (618, 1020, 1104, 1450)), (4, 1): (4, (1101, 1721, 1602, 2355)), (10, 4): (10, (125, 1507, 617, 1936)), (7, 1): (7, (1100, 1719, 1601, 2353)), (12, 7): (12, (119, 1671, 614, 2165)), (17, 1): (17, (618, 1740, 1104, 2012)), (15, 10): (15, (118, 318, 611, 809)), (19, 2): (19, (606, 956, 1102, 1229)), (18, 6): (18, (615, 321, 1107, 749)), (15, 7): (15, (118, 1979, 611, 2415)), (1, 0): (1, (606, 755, 1103, 968)), (3, 5): (3, (121, 315, 615, 813)), (2, 7): (2, (610, 318, 1107, 1247)), (8, 3): (8, (1107, 1423, 1598, 1755)), (9, 2): (9, (1100, 313, 1603, 1728)), (6, 1): (6, (1101, 1718, 1603, 2351)), (16, 1): (16, (1099, 327, 1601, 1727)), (12, 4): (12, (1100, 953, 1602, 1289)), (15, 9): (15, (118, 813, 611, 1300)), (14, 3): (14, (606, 318, 1105, 2574)), (19, 1): (19, (121, 2164, 612, 2436)), (0, 2): (0, (610, 317, 1107, 2576)), (1, 3): (1, (606, 322, 1103, 717)), (3, 0): (3, (609, 755, 1107, 964)), (2, 8): (2, (123, 318, 616, 1678)), (8, 0): (8, (618, 2233, 1104, 2443)), (6, 2): (6, (1101, 321, 1603, 1724)), (12, 9): (12, (119, 311, 614, 1677)), (18, 1): (18, (615, 1739, 1107, 2011)), (8, 10): (8, (129, 324, 613, 1679)), (5, 0): (5, (123, 1011, 615, 1424)), (10, 0): (10, (611, 1535, 1108, 1743)), (12, 3): (12, (1100, 626, 1602, 959)), (17, 5): (17, (618, 327, 1104, 751)), (13, 2): (13, (1101, 315, 1604, 1731)), (19, 6): (19, (121, 804, 612, 1442)), (18, 2): (18, (615, 834, 1107, 1106)), (17, 10): (17, (129, 809, 614, 1302)), (15, 3): (15, (1100, 318, 1602, 683)), (1, 4): (1, (119, 1509, 612, 1937)), (2, 3): (2, (1101, 1145, 1603, 1542)), (8, 7): (8, (1107, 629, 1598, 1055)), (4, 2): (4, (1101, 330, 1602, 1727)), (5, 3): (5, (609, 327, 1106, 2573)), (10, 5): (10, (125, 1975, 617, 2409)), (7, 0): (7, (122, 1012, 615, 1423)), (12, 0): (12, (608, 2236, 1106, 2448)), (17, 0): (17, (618, 1536, 1104, 1746)), (19, 5): (19, (121, 314, 612, 810)), (18, 7): (18, (126, 1978, 612, 2413)), (15, 6): (15, (605, 2050, 1106, 2477)), (3, 4): (3, (121, 1652, 615, 2083)), (2, 4): (2, (610, 1452, 1107, 1884)), (8, 4): (8, (1107, 1093, 1598, 1431)), (9, 1): (9, (1100, 1722, 1603, 2358)), (11, 2): (11, (610, 321, 1107, 2570)), (10, 6): (10, (611, 317, 1108, 751)), (16, 2): (16, (610, 327, 1105, 2572)), (12, 5): (12, (608, 1801, 1106, 2198)), (17, 3): (17, (618, 2050, 1104, 2415)), (15, 8): (15, (605, 318, 1106, 749)), (14, 0): (14, (119, 1010, 612, 1423)), (19, 0): (19, (606, 753, 1102, 962)), (18, 8): (18, (126, 816, 612, 1302)), (15, 5): (15, (118, 1508, 611, 1940)), (1, 2): (1, (606, 962, 1103, 1232)), (3, 3): (3, (609, 315, 1107, 715)), (8, 1): (8, (1107, 324, 1598, 590)), (6, 3): (6, (613, 321, 1107, 2568)), (11, 1): (11, (1101, 321, 1604, 1728)), (0, 0): (0, (123, 1012, 616, 1425)), (10, 1): (10, (611, 1737, 1108, 2008)), (17, 4): (17, (618, 1103, 1104, 1496)), (13, 1): (13, (1101, 1725, 1604, 2358)), (18, 3): (18, (615, 1100, 1107, 1496)), (17, 9): (17, (1107, 327, 1599, 809)), (15, 2): (15, (605, 1739, 1106, 2012)), (2, 0): (2, (1101, 1581, 1603, 1790)), (8, 8): (8, (129, 1673, 613, 2163)), (4, 3): (4, (611, 330, 1107, 2571)), (5, 2): (5, (1100, 327, 1602, 1727)), (10, 2): (10, (611, 833, 1108, 1105))}, [], lambda x: x)
    app.MainLoop()
