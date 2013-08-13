import pdb, traceback
import wx, wx.lib.scrolledpanel, wx.lib.intctrl
import os, sys
from os.path import join as pathjoin
from sets import Set
from PIL import Image
import csv
try:
    import cPickle as pickle
except ImportError:
    import pickle
import re
import numpy as np
import scipy.misc
from collections import Counter

from group_contests import final_grouping, extend_multibox, intersect, group_given_contests,get_target_to_contest
from verifycontestgrouping import VerifyContestGrouping

sys.path.append('..')
from util import ImageManipulate
import util, config

from wx.lib.pubsub import Publisher

class LabelContest(wx.Panel):
    def __init__(self, parent, size):
        if not parent: return
        wx.Panel.__init__(self, parent, id=-1, size=size)

        self.parent = parent
        self.canMoveOn = False

        # a dict mapping:
        #  {(ballotid, contestid): 
        self.text = {}
        
        Publisher().subscribe(self.getproj, "broadcast.project")
    
    def getproj(self, msg):
        self.proj = msg.data

    def gatherData(self):
        """
        Get the data from the files.
        This includes the location of the template files, as well as
        how the targets are grouped together.
        """
        self.dirList = []
        # Maps {groupID: [csvpath_side0, ...]}
        group_targets_map = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                      self.proj.group_targets_map),
                                                 'rb'))
        # GROUP_TO_BALLOTS: {int groupID: [int ballotID_i, ...]}
        group_to_ballots = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                     self.proj.group_to_ballots), 'rb'))
        # GROUP_EXMPLS: {int groupID: [int ballotID_i, ...]}
        group_exmpls = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                 self.proj.group_exmpls), 'rb'))
        b2imgs = pickle.load(open(self.proj.ballot_to_images, 'rb'))

        img2page = pickle.load(open(pathjoin(self.proj.projdir_path,
                                             self.proj.image_to_page), 'rb'))
        # TARGET_LOCS_MAP: maps {int groupID: {int page: [CONTEST_i, ...]}}
        target_locs_map = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                    self.proj.target_locs_map), 'rb'))

        self.flipped = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                 self.proj.image_to_flip), 'rb'))

        if os.path.exists(pathjoin(self.proj.projdir_path, 'quarantinedgroups_seltargets.p')):
            groups_quar = set(pickle.load(open(pathjoin(self.proj.projdir_path, 'quarantinedgroups_seltargets.p'))))
        else:
            groups_quar = set()
        quar_groups = pickle

        # groupedtargets is [[[(targetid,contestid,left,up,right,down)]]]
        # where:
        #   groupedtargets[a][b][c] is the ID and location of target C in contest B of template A
        #   len(groupedtargets) is the number of templates
        #   len(groupedtargets[a]) is the number of contests in template A
        #   len(groupedtargets[a][b]) is the number of targets in contest B of template A

        self.groupedtargets = []
        
        for groupID, contests_sides in target_locs_map.iteritems():

            if groupID not in group_exmpls:
                # All ballots in this partition had errors. Skip it.
                # TODO this may crash when multi-sided ballots have errors
                #self.groupedtargets.append([])
                continue

            if groupID in groups_quar:
                # This is a group that was quarantined ('flagged') during SelectTargets
                continue
            # Grab an arbitrary exemplar image from this group
            imgpaths = b2imgs[group_exmpls[groupID][0]]
            imgpaths_ordered = sorted(imgpaths, key=lambda imP: img2page[imP])
            for side, contests in contests_sides.iteritems():
                exmpl_imP = imgpaths_ordered[side]
                if self.dirList == []:
                    self.template_width, self.template_height = Image.open(exmpl_imP).size

                self.dirList.append(exmpl_imP)
                gr = {} # maps {int contestID: [[id, contest_id, x1, y1, x2, y2], ...]}
                for contest in contests:
                    contestbox, targetboxes = contest[0], contest[1:]
                    for tbox in targetboxes:
                        # TBOX := [x1, y1, w, h, id, contest_id]
                        gr.setdefault(tbox[5], []).append((tbox[4], tbox[5],
                                                           tbox[0], tbox[1],
                                                           tbox[0] + tbox[2],
                                                           tbox[1] + tbox[3]))
                lst = gr.values()
                if not lst:
                    # Means this file had no contests, so, add dummy 
                    # values to my data structures
                    # Grab an arbitrary voted ballot from this group
                    #imgpaths = b2imgs[group_exmpls[groupID][0]]
                    #imgpaths_ordered = sorted(imgpaths, key=lambda imP: img2page[imP])
                    #self.dirList.append(imgpaths_ordered[side])
                    self.groupedtargets.append([])
                    continue
                # Figure out where the columns are.
                # We want to sort each group going left->right top->down
                #   but only go left->right if we're on a new column,
                #   not if we're only off by a few pixels to the left.
                errorby = self.template_width / 20
                #errorby = 0.05
    
                cols = {}
                for _,_,x,_,_,_ in sum(lst, []):
                    found = False
                    for c in cols:
                        if abs(c-x) < errorby:
                        #if (abs(c-x)/self.template_width) < errorby:
                            found = True
                            cols[x] = cols[c]
                            break
                    if not found:
                        cols[x] = x

                # And sort by columns within each contest
                lst = [sorted(x, key=lambda x: (cols[x[2]], x[3])) for x in lst]
                # And then sort each contest in the same way, globally
                slist = sorted(lst, key=lambda x: (cols[x[0][2]], x[0][3]))

                self.groupedtargets.append(slist)

    def maybe_flip(self, path):
        img = Image.open(path).convert("RGB")
        if self.flipped[path]:
            img = img.rotate(180)
        return np.array(img)


    def reset_panel(self):
        self.proj.removeCloseEvent(self.save)
    
    def reset_data(self):
        for f in [self.proj.contest_id, 
                  self.proj.contest_internal, 
                  self.proj.contest_text]:
            if os.path.exists(f):
                print "UNLINK", f
                os.unlink(f)

    firstTime = True

    def start(self, sz=None):
        """
        Set everything up to display.
        """
        if not self.firstTime: return

        self.firstTime = False

        print "SET UP", sz
        self.thesize = sz

        sizer = wx.BoxSizer(wx.HORIZONTAL)
        self.sizer = sizer

        self.small_x_size = 303
        self.small_y_size = 500
        self.view_x_size = sz[0]-300-self.small_x_size-100
        self.view_y_size = sz[1]-100

        sz2 = wx.BoxSizer(wx.VERTICAL)
        self.imagebox = ImageManipulate(self, size=(self.view_x_size,self.view_y_size))

        sz3 = wx.BoxSizer(wx.HORIZONTAL)
        zoomin = wx.Button(self, label="Zoom In")
        zoomout = wx.Button(self, label="Zoom Out")
        zoomin.Bind(wx.EVT_BUTTON, lambda x: self.imagebox.zoomin())
        zoomout.Bind(wx.EVT_BUTTON, lambda x: self.imagebox.zoomout())

        sz3.Add(zoomin)
        sz3.Add(zoomout)
        sz2.Add(self.imagebox)
        sz2.Add(sz3)
        sizer.Add(sz2)

        rightside = wx.BoxSizer(wx.HORIZONTAL)

        #self.textarea = wx.Panel(self)
        self.textarea = wx.lib.scrolledpanel.ScrolledPanel(self, size=(300, self.view_y_size-150))
        self.textarea.SetAutoLayout(True)
        self.textarea.SetupScrolling(False, True)

        self.proj.addCloseEvent(self.save)

        self.count = 0
        self.templatenum = 0
        
        self.gatherData()

        self.grouping_cached = None
        self.getValues()

        self.text_targets = []

        self.canMoveOn = False

        textbox = wx.BoxSizer(wx.VERTICAL)

        button1 = wx.Button(self, label='Previous Contest')
        button2 = wx.Button(self, label='Next Contest')
        button2.Bind(wx.EVT_BUTTON, lambda x: self.doadd(1))
        button22 = wx.Button(self, label='Next Unfilled Contest')
        button1.Bind(wx.EVT_BUTTON, lambda x: self.doadd(-1))
        button22.Bind(wx.EVT_BUTTON, self.nextunfilled)

        textbox.Add(self.textarea)
        textbox.Add(button1)
        textbox.Add(button2)
        textbox.Add(button22)

        self.remainingText = wx.StaticText(self, style=wx.TE_READONLY, size=(150,30))
        self.curBlankBallotNum = wx.StaticText(self, style=wx.TE_READONLY)
        textbox.Add(self.remainingText)
        textbox.Add(self.curBlankBallotNum)

        template = wx.BoxSizer(wx.VERTICAL)
        button3 = wx.Button(self, label='Previous Style')
        button4 = wx.Button(self, label='Next Style')
        button3.Bind(wx.EVT_BUTTON, lambda x: self.nexttemplate(-1))
        button4.Bind(wx.EVT_BUTTON, lambda x: self.nexttemplate(1))


        self.templatebox = wx.Panel(self, size=(self.small_x_size,self.small_y_size))
        self.templatebox.img = wx.StaticBitmap(self.templatebox)
        
        template.Add(self.templatebox)
        template.Add(button3)
        template.Add(button4)

        if os.path.exists(self.proj.patch_loc_dir):
            attr_data = {}
            blankballot_attrlocs = os.listdir(self.proj.patch_loc_dir)
            util.sort_nicely(blankballot_attrlocs)
            for f in blankballot_attrlocs:
                attrs = []
                for line in open(os.path.join(self.proj.patch_loc_dir, f)):
                    line = line.split(",")
                    attrs.append((line[6], line[7]))
                attr_data[line[0]] = tuple([x[1] for x in sorted(attrs[1:])])
                attr_titles = [x[0] for x in sorted(attrs[1:])]
            def find_next_regex(x=None):
                popup = wx.TextEntryDialog(None, "Enter the regex to match (filename|"+ ("|".join(map(str,attr_titles))) +") where | is a newline", 'Title', '.*|.*|.*')
    
                if popup.ShowModal() == wx.ID_OK:
                    val = popup.GetValue()
                    val = val.split("|")
                    match = set([k for k,v in attr_data.items() if all(re.match(x, y) for x,y in zip(val,[k]+list(v)))])
                    for time in range(2):
                        did = False
                        for i,x in enumerate(self.dirList):
                            if time == 1 or i > self.templatenum and x in match:
                                print "NEXT", i-self.templatenum
                                self.nexttemplate(i-self.templatenum)
                                did = True
                                break
                        if did: break
                    
                    
    
            regexnext = wx.Button(self, label='Next Regex-Matching Ballot')
            regexnext.Bind(wx.EVT_BUTTON, find_next_regex)
    
            template.Add(regexnext)

        def goto_num(x=None):
            popup = wx.TextEntryDialog(None, "Enter the style number to jump to", 'Title', '')
    
            if popup.ShowModal() == wx.ID_OK:
                val = popup.GetValue()
                self.nexttemplate((int(val)-self.templatenum) - 1)

        goto = wx.Button(self, label='Jump to style number...')
        goto.Bind(wx.EVT_BUTTON, goto_num)
    
        template.Add(goto)
    
        button6 = wx.Button(self, label="Detect Contest Duplicates...")
        button6.Bind(wx.EVT_BUTTON, self.compute_equivs)
        template.Add(button6)

        @util.pdb_on_crash
        def addmultibox(x):
            orders = []
            for bid in range(len(self.grouping_cached)):
                order = []
                for cid in range(len(self.grouping_cached[bid])-1):
                    #print (bid,cid)
                    #print self.multiboxcontests
                    if any((bid,self.contest_order[bid][cid+1]) in mult for mult in self.multiboxcontests):
                        continue
                    if any((bid,self.contest_order[bid][cid+1]) in mult for mult in self.multiboxcontests):
                        continue
                    m1 = self.mapping_inverse[(bid,self.contest_order[bid][cid])]
                    m2 = self.mapping_inverse[(bid,self.contest_order[bid][cid+1])]
                    order.append((m1,m2))
                orders.append(order)
            #print "ORDS", orders
            #print "inv", self.mapping_inverse
            if any(any((self.templatenum, self.contest_order[self.templatenum][self.count+x]) in y for y in self.multiboxcontests) for x in range(2)): return
            extension, newgroup = extend_multibox(self.grouping_cached,
                                        self.mapping_inverse[(self.templatenum, self.contest_order[self.templatenum][self.count])],
                                        self.mapping_inverse[(self.templatenum, self.contest_order[self.templatenum][self.count+1])],
                                        orders)
            #print "EXTENSION", extension
            #print "NEWGROUP", newgroup
            self.multiboxcontests_enter += [tuple([(self.mapping[x][0], self.contest_order[self.mapping[x][0]].index(self.mapping[x][1])) for x in pair]) for pair in extension]
            
            #print "MULTIBOX"
            #print self.multiboxcontests_enter

            boxes_in_new_group = [bid_cid for pair in extension for bid_cid in pair]
            cleared = []
            for i,group in enumerate(self.groups_saved):
                print group[0]
                new_group = []
                for ((bid,boxes),order) in group:
                    if (bid,boxes[0]) not in boxes_in_new_group:
                        new_group.append(((bid,boxes),order))
                if new_group != []:
                    cleared.append(new_group)
            fixed = cleared + [[((bid,boxes),order) for ((bid,boxes,text),order) in newgroup]]
            #newvalids[len(cleared)] = [[self.mapping[bid,bb[0]] for ((bid,bb,_),_) in newgroup]]
            self.groups_saved = fixed

            #print "BEFORE", self.equivs_processed
            self.compute_equivs_2(run_verification=False)
            #print "AFTER", self.equivs_processed

            def putresults(get_result):
                ids_in_new_group = get_result[0]
                # HACK -- WE DON'T USE THE VERIFICATION STUFF AT ALL
    
                old = self.equivs_processed
                #print "OLD", self.equivs_processed
                new_processed = []
                for each in self.equivs_processed:
                    new_each = [x for x in each if x not in ids_in_new_group]
                    if new_each != []:
                        new_processed.append(new_each)
                new_processed.append(ids_in_new_group)
                self.equivs_processed = new_processed
                #print "NEW", self.equivs_processed
                #print "DIFF"
                #for a in self.equivs_processed:
                #    if a not in old:
                #        print a
    
            ids_in_new_group = [self.mapping[x] for x in boxes_in_new_group]

            print 'verify here'
            VerifyContestGrouping(self.proj.ocr_tmp_dir, self.dirList, [ids_in_new_group], self.reorder, self.reorder_inverse, self.mapping, self.mapping_inverse, self.multiboxcontests, putresults)

            return

        button6 = wx.Button(self, label="Mark as Multi-Box...")
        button6.Bind(wx.EVT_BUTTON, addmultibox)
        template.Add(button6)


        def clear_names(evt):
            """ Clears all text input widgets for candidate names. """
            for cbox_name in self.text_targets:
                cbox_name.SetValue("")
            self.Layout()
        button_clearnames = wx.Button(self, label="Clear Names")
        button_clearnames.Bind(wx.EVT_BUTTON, clear_names)
        template.Add(button_clearnames)

        if self.proj.devmode:
            button5 = wx.Button(self, label="Magic \"I'm Done\" Button")
            if not config.IS_DEV:
                button5.Hide()
            def declareReady(x):
                dlg = wx.MessageDialog(None, "Are you sure?\nThis will destroy all text you have entered.", style=wx.YES_NO | wx.NO_DEFAULT)
                status = dlg.ShowModal()
                if status == wx.ID_NO: return
                self.save()
                for ct,cid_lst in enumerate(self.contest_order):
                    for cid in cid_lst:
                        numt = len(self.groupedtargets[ct][cid])
                        title = "_".join(["title", str(ct), str(cid)])
                        contests = ["_".join(["contest", str(ct), str(cid), str(targ)]) for targ in range(numt)]
                        self.text[ct,cid] = [title]+contests
                        self.voteupto[ct, cid] = 1
                print "TEXT NOW", self.text
                self.restoreText()
                self.canMoveOn = True
                Publisher().sendMessage("broadcast.can_proceed")
            button5.Bind(wx.EVT_BUTTON, declareReady)
            template.Add(button5)

        rightside.Add(textbox)
        rightside.Add((20,-1))
        rightside.Add(template)

        # If set to true, don't restore text.
        self.doNotClear = False

        self.nexttemplate(0)

        sizer.Add(rightside, wx.ALL|wx.EXPAND, 5)
        self.SetSizer(sizer)

        sizer.Fit(self)
        self.Layout()
        self.Fit()
 
        self.Show()

    def load_languages(self):
        """ Returns a mapping from imgpath -> language. """
        def get_language(d):
            tries = ('language', 'lang', 'Language', 'Lang')
            for thing in tries:
                if thing in d:
                    return d[thing]
            return None
        bal2grp = pickle.load(open(pathjoin(self.proj.projdir_path,
                                            self.proj.ballot_to_group), 'rb'))
        grp2bals = pickle.load(open(pathjoin(self.proj.projdir_path,
                                            self.proj.group_to_ballots), 'rb'))
        bal2imgs = pickle.load(open(self.proj.ballot_to_images, 'rb'))
        # GROUP2INFO: {int groupID: {attrtype: attrval}}
        group2info = pickle.load(open(pathjoin(self.proj.projdir_path,
                                               self.proj.group_infomap), 'rb'))
        lang2tesseract = {'english': 'eng', 'eng': 'eng', 'en': 'eng',
                          'spanish': 'spa', 'span': 'spa', 'esp': 'spa', 
                          'korean': 'kor', 'kor': 'kor', 
                          'chi': 'chi_sim', 'chinese': 'chi_sim', 
                          'vietnamese': 'vie'}
        result = {} # {str imgpath: str language}
        for groupid, infodict in group2info.iteritems():
            found_language = get_language(infodict)
            cur_language = lang2tesseract.get(found_language, None)
            if cur_language != None:
                ballotids = grp2bals[groupid]
                for ballotid in ballotids:
                    imgpaths = bal2imgs[ballotid]
                    for imgpath in imgpaths:
                        result[imgpath] = cur_language
        return result

    def compute_equivs(self, x):
        if config.TIMER:
            config.TIMER.start_task("LabelContests_ComputeEquivClasses_CPU")
        self.has_equiv_classes = True
        languages = self.load_languages()

        # Regroup the targets so that equal contests are merged.
        targets = []
        did = {}
        for bid,ballot in enumerate(self.groupedtargets):
            ballotlist = []
            for gid,targlist in enumerate(ballot):
                if (bid, gid) in did: continue
                if any((bid, gid) in x for x in self.multiboxcontests_enter):
                    # These are the ones we will merge
                    use = [x for x in self.multiboxcontests_enter if (bid, gid) in x][0]
                    tmp = []
                    for b,g in use:
                        tmp += self.groupedtargets[b][g]
                        did[b,g] = True
                    ballotlist.append([x[2:] for x in tmp])
                else:
                    ballotlist.append([x[2:] for x in targlist])
                    did[bid,gid] = True
            targets.append(ballotlist)

        #print "ALL", targets
        if self.grouping_cached:
            groups = final_grouping(self.grouping_cached, targets, self.dirList, self.load_languages(), t=self.proj.ocr_tmp_dir)
        else:
            if not self.proj.infer_bounding_boxes:
                dlg = wx.MessageDialog(self, message="You must auto-detect bounding boxes in select-and-group-targets to run the inference.", style=wx.OK)
                dlg.ShowModal()
                return

            vendor = self.proj.vendor_obj if 'vendor_obj' in self.proj.vals else None
            ballots, groups = group_given_contests(self.proj.ocr_tmp_dir, 
                                                   self.dirList, targets, 
                                                   self.boxes, 
                                                   self.flipped,
                                                   vendor,
                                                   languages,
                                                   NPROC=None)
            self.grouping_cached = ballots
            #print "CACHED", ballots

        self.groups_saved = groups
        self.compute_equivs_2()
    
    def compute_equivs_2(self, run_verification=True):
        groups = self.groups_saved
        #print "GROUPS IS", groups

        gr = [[(b[0][0],b[0][1]) for b in group] for group in groups]

        #print gr
        mapping = {}
        # Parallelize this!
        for ballot_count, ballot in enumerate(self.groupedtargets):
            print 'on ballot', ballot_count
            # All of the bounding boxes for a ballot.
            contestbboxes = [x[1] for x in sum(gr, []) if x[0] == ballot_count]
            #print 'bboxes', contestbboxes
            for targetlist in ballot:
                #print 'picking rep ', targetlist[0][2:]
                flattencontests = sum(contestbboxes,[])
                targ_to_cont = get_target_to_contest(flattencontests, [x[2:] for x in targetlist])
                corresponding_boxes = [flattencontests[x] for x in targ_to_cont.values()]
                w = [i for i,bboxes in enumerate(contestbboxes) if any(x in corresponding_boxes for x in bboxes)]
                #w = [i for i,bblist in enumerate(contestbboxes) if any(intersect(targetlist[0][2:], x) == targetlist[0][2:] for x in bblist)]
                if len(w) != 1:
                    print 'I got', w, 'of them'
                    print [bblist for i,bblist in enumerate(contestbboxes) if any(intersect(targetlist[0][2:], x) == targetlist[0][2:] for x in bblist)]
                    print 'gr', gr
                    print 'mapping', mapping
                    print 'contest bboxes', contestbboxes
                    print 'targetlist', targetlist
                    print "OH NO SOMETHING WENT WRONG"
                    pdb.set_trace()
                    raise Exception("OH NO SOMETHING WENT WRONG")
                #print 'w', w
                #print 'contest', targetlist[0][1], 'corresponds to', contestbboxes[w[0]]
                for bbox in contestbboxes[w[0]]:
                    mapping[ballot_count, bbox] = (ballot_count, targetlist[0][1])
        self.mapping = mapping
        self.mapping_inverse = dict((v,k) for k,v in mapping.items())

        reorder = {}
        reorder_inverse = {}
        for group in [[(x[0][0],x[0][1], x[1]) for x in g] for g in groups]:
            first = (group[0][0], group[0][1][0])
            reorder[mapping[first]] = {}
            for ballotid, contests, order in group:
                contest = contests[0]
                reorder[mapping[first]][mapping[ballotid,contest]] = order
                reorder_inverse[mapping[ballotid, contest]] = mapping[first]
        self.reorder = reorder
        self.reorder_inverse = reorder_inverse

        self.multiboxcontests = [[(c,self.contest_order[c][b]) for c,b in y] for y in self.multiboxcontests_enter]

        self.equivs = [[mapping[bid,bboxes[0]] for bid,bboxes in group] for group in gr]
        
        #print "MAPPING", self.mapping
        #print "MAPPING_INVERSE", self.mapping_inverse
        #print "REORDER", self.reorder
        #print "REORDER_INVERSE", self.reorder_inverse
        #print "EQUIVS", self.equivs
        #pdb.set_trace()

        def putresults(data):
            if config.TIMER:
                config.TIMER.stop_task("LabelContests_VerifyContestGrouping_H")
            print "I get the data", data
            self.equivs_processed = data
            print "(ComputeEquivClasses) Done with verify contest grouping and infer contests."

        if config.TIMER:
            config.TIMER.stop_task("LabelContests_ComputeEquivClasses_CPU")

        dlg = wx.MessageDialog(self, style=wx.OK,
                               message="Contest duplicate detection complete!")
        dlg.ShowModal()

        if any(len(x) > 1 for x in self.equivs) and run_verification:
            print "RUN"
            if config.TIMER:
                config.TIMER.start_task("LabelContests_VerifyContestGrouping_H")
            VerifyContestGrouping(self.proj.ocr_tmp_dir, self.dirList, self.equivs,
                                  self.reorder, self.reorder_inverse, self.mapping, self.mapping_inverse,
                                  self.multiboxcontests, putresults,
                                  NPROC=None)
        else:
            print "(Info) No equiv groups found."
        print "(ComputeEquivClasses) Done."

    def stop(self):
        self.save()

    def save(self):
        self.saveText(removeit=False)

        print "Label Contest Saving"
        did_multibox = {}
        groupedtext = {}
        for k in self.text.keys():
            if k in did_multibox: continue
            t = []
            did_multibox[k] = []
            for each in self.continued_contest(k):
                did_multibox[k].append(each)
                t += self.text[each][1:]
            if self.text[k]:
                groupedtext[k] = [self.text[k][0]]+t
            
        #print did_multibox

        # We want to figure out which contests are "equal"
        #  so that when we tally votes we report them together.
        # Equality is defined as having all the same text.


        # (bid,cid) tuples
        equal = []
        used = {}

        for k1,v1 in groupedtext.items():
            if k1 in used: continue
            eq = []
            for k2,v2 in groupedtext.items():
                if k2 in used: continue
                if [x.lower() for x in v1] == [x.lower() for x in v2]:
                    it = self.contestID[k2]
                    eq.append((it[0], it[1]))
                    used[k2] = True
            equal.append(eq)
            used[k1] = True

        c_id = csv.writer(open(self.proj.contest_id, "w"))
        # path, ID in select-and-group-targets file, new ID, ordering

        print "Step 1"
        mapping = {}
        for num,group in enumerate(equal):
            for item in group:
                #print "ITEM", item
                mapping[item] = num
                ids = []
                for each in self.continued_contest(item):
                    # We need to get the contest ID in the new list
                    targets = [x for x in self.groupedtargets[each[0]] if x[0][1] == each[1]][0]
                    ids += [str(x[0]) for x in targets]
                for cont in did_multibox[each]:
                    # Save it for all boxes in the contest.
                    c_id.writerow([self.dirList[cont[0]],cont[1],num]+ids)

        # We write out the result as a mapping from Contest ID to text
        id_to_text = {}
        for k,v in groupedtext.items():
            bid, cid = self.contestID[k]
            id_to_text[(bid, cid)] = [str(self.voteupto[k])]+v

        fout = csv.writer(open(self.proj.contest_text, "w"))

        did = {}
        for k,v in id_to_text.items():
            if mapping[k] not in did:
                # ContestID, upto, title, (label)*
                fout.writerow([mapping[k]]+v)
                did[mapping[k]] = True
        print "Step 2"

        pickle.dump((self.text, self.voteupto, self.grouping_cached), open(self.proj.contest_internal, "w"))
        if self.has_equiv_classes:
            pickle.dump((self.mapping, self.mapping_inverse, self.reorder, self.reorder_inverse, self.equivs, self.groups_saved, self.grouping_cached, self.multiboxcontests, self.multiboxcontests_enter, self.equivs_processed), open(self.proj.contest_grouping_data, "w"))
        print "Done"

                    
    def setupBoxes(self):
        self.proj.infer_bounding_boxes = True
        if self.proj.infer_bounding_boxes:
            res = []
            target_locs_map = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                        self.proj.target_locs_map), 'rb'))
            for groupID, contests_sides in target_locs_map.iteritems():
                for side, contests in sorted(contests_sides.iteritems(), key=lambda t: t[0]):
                    ballot = []
                    for contest in contests:
                        # CBOX := [x1, y1, w, h, id, contest_id]
                        cbox, tboxes = contest[0], contest[1:]
                        entry = (cbox[4], cbox[0], cbox[1], 
                                 cbox[0] + cbox[2], cbox[1] + cbox[3])
                        ballot.append(entry)
                    res.append(ballot)
            #print "LOADING", res
            # When we load from select-and-group-targets, the order we
            # get isn't the adjusted ordering. We need to correct the
            # order so that we can work with it.
            correctorder = [[y[0][1] for y in x] for x in self.groupedtargets]

            self.boxes = []
            for i,(ballot,order) in enumerate(zip(res,correctorder)):
                #print i
                boxes = []
                for o in order:
                    try:
                        boxes.append([x for x in ballot if x[0] == o][0])
                    except Exception as e:
                        traceback.print_exc()
                        pdb.set_trace()
                self.boxes.append(boxes)
            #print self.boxes
            return

        self.boxes = []
        def bound(targetlst, goleft, width):
            l = u = 2**32
            r = d = 0
            for _,ID,ll,uu,rr,dd in targetlst:
                l = min(ll,l)
                u = min(uu,u)
                d = max(dd,d)
                r = max(rr,r)
            return ID, l-goleft,u-int(.06*self.template_height), l+width,d+int(.03*self.template_height)
        
        # The (id,l,u,r,d) tuple for each contest of each template

        for i,ballot in enumerate(self.groupedtargets):
            ballotw = self.template_width
            columns = {}
            for group in ballot:
                for target in group:
                    if not any([target[2] + x in columns for x in range(-5,5)]):
                        columns[target[2]] = True
            columns = sorted(columns.keys())
            if len(columns) == 0:
                # We have a blank ballot with no contests
                self.boxes.append([])
                continue
            leftmargin = min(columns)
            # Interior space available
            remaining = max(ballotw-(2*leftmargin), 0.10*self.template_height)
            # The size of one box
            boxwidth = remaining/len(columns)
            boxwidth = min(boxwidth, self.template_width/2)
            goleft = 0
            if len(columns) >= 2:
                goleft = max(0,columns[1]-(columns[0]+boxwidth))

            bboxes = [bound(x,goleft,boxwidth) for x in ballot]
            #print "I THINK BBOX", bboxes
            # TODO shouldn't extend in to next column

            self.boxes.append(bboxes)


    def getValues(self):
        """
        Set up all the variables
        """

        # The text that the user enters.
        # Keys are of the form templateid:(l,u,r,d)
        self.text = {}
        self.voteupto = {}

        restored = False
        if os.path.exists(self.proj.contest_internal):
            if open(self.proj.contest_internal).read():
                restored = True
                self.text, self.voteupto, self.grouping_cached = pickle.load(open(self.proj.contest_internal))

        self.equivs = []
        self.has_equiv_classes = False
        self.multiboxcontests = []
        self.multiboxcontests_enter = []
        self.equivs_processed = []

        if os.path.exists(self.proj.contest_grouping_data):
            if open(self.proj.contest_grouping_data).read():
                print 'GOT THE DATA'
                dat = pickle.load(open(self.proj.contest_grouping_data))
                if len(dat) == 9:
                    self.mapping, self.mapping_inverse, self.reorder, self.reorder_inverse, self.equivs, self.groups_saved, self.grouping_cached, self.multiboxcontests, self.multiboxcontests_enter = dat
                else:
                    self.mapping, self.mapping_inverse, self.reorder, self.reorder_inverse, self.equivs, self.groups_saved, self.grouping_cached, self.multiboxcontests, self.multiboxcontests_enter, self.equivs_processed = dat
                self.has_equiv_classes = True

        # The PIL image for the contest.
        # Keys are of the form templateid:(l,u,r,d)
        self.crop = {}
        self.resize = {}

        self.groups = []

        self.setupBoxes()

        # Convert the ballot:boundingbox -> (ballotid, contestid)
        self.contestID = {}

        maxw,maxh = self.thesize
        # self.boxes is
        for i,each in enumerate(self.boxes):
            for x in each:
                if not restored:
                    self.text[i,x[0]] = []
                    self.voteupto[i,x[0]] = 1
                factor = 1
                try:
                    self.crop[i,x[0]] = (self.dirList[i],
                                         (x[1], x[2], 
                                          int((x[3]-x[1])*factor+x[1]),
                                          int((x[4]-x[2])*factor+x[2])))
                except Exception as e:
                    print e
                    pdb.set_trace()
                self.contestID[i,x[0]] = (i, x[0])

        self.contest_order = [[y[0] for y in x] for x in self.boxes]
        self.boxes = [[y[1:] for y in x] for x in self.boxes]
        #print "CROP", self.crop

        self.currentcontests = []

    
    def nexttemplate(self, ct):
        """
        Load up the next template.
        Make sure to save everything, then clear all the data.
        """
        self.save()

        if self.templatenum+ct >= len(self.dirList) or self.templatenum+ct < 0:
            self.templatenum = max(self.templatenum, 0)
            self.templatenum = min(self.templatenum, len(self.dirList)-1)
            # Don't do anything bad.
            return

        if self.currentcontests != []:
            self.saveText()

        self.currentcontests = []
        self.templatenum += ct

        if len(self.groupedtargets[self.templatenum]) == 0:
            # No contests, so skip it
            print "Skipping the empty blank template:", self.templatenum
            self.nexttemplate(1)
            return

        # Save the image corresponding to this template
        self.imgo = self.maybe_flip(self.dirList[self.templatenum])
        print 'qqq', self.imgo.shape
        self.imgo_resize = scipy.misc.imresize(self.imgo,(self.small_y_size, self.small_x_size))
        self.imgo_resizefactor_y = float(self.imgo.shape[0])/self.imgo_resize.shape[0]
        self.imgo_resizefactor_x = float(self.imgo.shape[1])/self.imgo_resize.shape[1]
        
        for cid in self.contest_order[self.templatenum]:
            # Fill in the current contest keys to use to index in the hashtables.
            self.currentcontests.append((self.templatenum,cid))

        # Which contest we're on.
        self.count = 0

        # It's okay to clear things now.
        self.doNotClear = False

        print 'ballot switch restore'
        # Fill in any text we might have entered so far.
        #self.restoreText()
        print 'now do add'

        # Show everything.
        self.doadd(0, dosave=False)

    def updateTemplate(self):
        """
        Make the template image correspond to how it should.
        Color the current selected contest, as well as the ones we've seen so far.
        """
        #return
        img = np.array(self.imgo_resize)

        def fix(z):
            l,u,r,d = z
            return (l/self.imgo_resizefactor_x,
                    u/self.imgo_resizefactor_y,
                    r/self.imgo_resizefactor_x,
                    d/self.imgo_resizefactor_y)

        #print self.currentcontests
        #print sorted(self.text.keys())
        c = 0
        for l,u,r,d in self.boxes[self.templatenum]:
            l,u,r,d = fix((l,u,r,d))
            #print c
            #print self.currentcontests[c]
            #print self.currentcontests[c] in self.text
            if c == self.count:
                pass
            elif self.text[self.currentcontests[c]] != []:
                img[u:d, l:r] *= .5
                img[u:d, l:r] += np.array([0, 200, 0])*.5#dr.rectangle(box, fill=(0,200,0))
            else:
                img[u:d, l:r] *= .5
                img[u:d, l:r] += np.array([200, 0, 0])*.5#dr.rectangle(box, fill=(200,0,0))

            c += 1
        # Redraw the yellow on the current so it goes on top of everything else
        l,u,r,d = fix(self.boxes[self.templatenum][self.count])
        #dr.rectangle(self.boxes[self.templatenum][self.count], fill=(200,200,0))
        img[u:d, l:r] = self.imgo_resize[u:d, l:r]
        img[u:d, l:r] *= .5
        img[u:d, l:r] += np.array([200, 200, 0])*.5

        bothcontests = self.continued_contest(self.currentcontests[self.count])
        if len(bothcontests) > 1:
            nextbox = [x for x in bothcontests if x != self.currentcontests[self.count]][0]
            l,u,r,d = fix(self.boxes[nextbox[0]][self.contest_order[nextbox[0]].index(nextbox[1])])
            #dr.rectangle(, fill=(0,0,200))
            img[u:d, l:r] = self.imgo_resize[u:d, l:r]
            img[u:d, l:r] *= .5
            img[u:d, l:r] += np.array([0, 0, 200])*.5

        #new_template = pil2wxb(Image.blend(img,self.imgo,.5).resize((303, 500)))
            
        image = wx.EmptyImage(self.small_x_size, self.small_y_size)
        image.SetData(img.tostring())
        wxBitmap = image.ConvertToBitmap()

        self.templatebox.img.SetBitmap(wxBitmap)
        
        SCALE = float(self.imgo.shape[0])/self.small_y_size
        print "SCALE", SCALE
        # Switch to selected contest.
        @util.pdb_on_crash
        def foo(x):
            for i,(l,u,r,d) in enumerate(self.boxes[self.templatenum]):
                if l <= x.X*SCALE <= r and u <= x.Y*SCALE <= d:
                    print "Boxes are", self.boxes[self.templatenum]
                    print "And this is", (l,u,r,d)
                    i = self.boxes[self.templatenum].index((l,u,r,d))

                    self.doadd(i-self.count)
                    break
        self.templatebox.img.Bind(wx.EVT_LEFT_DOWN, lambda x: foo(x))

    def restoreText(self):
        if len(self.groupedtargets[self.templatenum]) == 0:
            return
        arr = self.text[self.currentcontests[self.count]]
        print "RESTORE", self.currentcontests[self.count], arr
        self.text_upto.SetValue(int(self.voteupto[self.currentcontests[self.count]]))
        # First check if we've filled in text here before.
        if len(arr) == len(self.text_targets)+1:
            # Yep, we have. Restore it.
            self.text_title.SetValue(arr[0])
            for i,each in enumerate(self.text_targets):
                # NO OFF BY ONE ERROR FOR YOU!
                each.SetValue(arr[i+1])
            print 'all is well'
        self.text_title.SetMark(0,0)
        self.text_title.SetInsertionPointEnd()


    def continued_contest(self, item):
        if any(item in x for x in self.multiboxcontests):
            return [x for x in self.multiboxcontests if item in x][0]
        else:
            return [item]

    def is_multibox_contest(self, contestid):
        """ Returns True if the given contest is part of a multibox contest,
        False o.w. 
        Input:
            tuple CONTESTID: (int STYLENUM, int ID)
        """
        return any([contestid in tuples for tuples in self.multiboxcontests])

    @util.pdb_on_crash
    def saveText(self, removeit=True):
        """
        Save the text associated with the current contest.

        We also look to see if this contest is in an equiv-class, and, if it is,
        then go ahead and automatically enter the text in the other contests.
        We may need to update the candidate order, since the contest might
        have randomized candidate ordering.
        """
        if len(self.groupedtargets[self.templatenum]) == 0:
            # No contests, so skip it
            return
        print "SAVING", self.templatenum, self.count
        #print self.currentcontests
        try:
            self.text_title.GetValue()
        except:
            # We haven't filled anything in yet. Just abort.
            return
        v = [self.text_title.GetValue()]+[x.GetValue() for x in self.text_targets]

        # Make sure no other contest on this ballot is the same
        for contest in self.currentcontests:
            if contest in self.text and sorted(self.text[contest]) == sorted(v) and contest != self.currentcontests[self.count]:
                dlg = wx.MessageDialog(self, message="Did not save; contest is a duplicate of previous contest on this ballot.", style=wx.OK)
                dlg.ShowModal()
                return

        if not all(x == '' for x in v):
            # We have entered at least something ... save it
            self.text[self.currentcontests[self.count]] = v
        else:
            self.text[self.currentcontests[self.count]] = []
        self.voteupto[self.currentcontests[self.count]] = self.text_upto.GetValue()        

        # Change the below 'if' test to 'True' if you want to disable
        # automated population of equiv-contests.
        if not self.has_equiv_classes:
            return
        


        #print "EQUAL ARE", self.equivs

        cur = self.currentcontests[self.count]
        #print 'This contest is', cur
        cur = self.continued_contest(cur)

        #print 'and now it is', cur
        
        #print 'txt', self.text

        if self.text[cur[0]] == []: return

        title = self.text[cur[0]][0]
        
        # This is a temporary hack.
        try:
            # Test if it's defined
            x = self.reorder_inverse
        except:
            equclass = [x for x in self.equivs if cur[0] in x][0]
            for each in equclass:
                self.text[each] = [title]
            return

        text = [self.text[x][1:] if self.text[x] != [] else ['']*len(self.groupedtargets[x[0]][self.contest_order[x[0]].index(x[1])]) for x in cur]
        text = sum(text, [])
        #print 'this', text

        cur_in_dict = [x for x in cur if x in self.reorder_inverse][0]
        set_repr = self.reorder_inverse[cur_in_dict]
        print 'set repr', set_repr
        reorder = self.reorder[set_repr][cur_in_dict]
        print "reorder", reorder
        adjusted = {}
        for i,t in enumerate(text):
            print 'sending', i, 'to', [x for x,y in reorder if y == i][0]
            adjusted[[x for x,y in reorder if y == i][0]] = t
        print adjusted
        print 'compare'
        print text
        text = [x[1] for x in sorted(adjusted.items())]
        print text
        
        if any(x in y for x in cur for y in self.equivs):
            #print 'yes'
            # Find the equivilance class
            eqclass = []
            for i,each in enumerate(self.equivs_processed):
                if any(x in cur for x in each):
                    eqclass = each
                    break
            #print 'diff', eqclass
            # Get the different one
            for continuation in eqclass:
                #print 'WORKING ON CONT', continuation
                continuation = self.continued_contest(continuation)
                
                #print 'assign to', continuation
                index = 0
                each_in_dict = [x for x in continuation if x in self.reorder[set_repr]][0]
                #print 'lookup', set_repr, each_in_dict
                #print self.reorder[set_repr]
                reorder = self.reorder[set_repr][each_in_dict]
                #print 'new reorder', reorder
                twiceadjusted = {}
                for i,t in enumerate(adjusted):
                    print i, [y for x,y in reorder if x == i]
                    twiceadjusted[[y for x,y in reorder if x == i][0]] = t
                #print 'setting', each, twiceadjusted
                newtext = [text[x[1]] for x in sorted(twiceadjusted.items())]
                #print 'is now', newtext


                for each in sorted(continuation, key=lambda x: self.contest_order[x[0]].index(x[1])):
                    size = len(self.groupedtargets[each[0]][self.contest_order[each[0]].index(each[1])])
                    #print 'assign', size, 'of them starting from', index, ':', [title]+newtext[index:index+size]
                    self.text[each] = [title]+newtext[index:index+size]
                    self.voteupto[each] = self.voteupto[self.currentcontests[self.count]]

                    index += size
            
        #print 'txtnow', self.text
        return

        if removeit:
            for each in self.text_targets:
                each.SetValue("")

    def changeCompleted(self, addone=0):
        didsofar = sum([x != [] for x in self.text.values()])+addone
        num = len(self.text.values())
        didsofar = min(didsofar, num)
        self.canMoveOn = didsofar == num
        if self.canMoveOn:
            Publisher().sendMessage("broadcast.can_proceed")
        
        self.remainingText.SetLabel("Completed %d of %d."%(didsofar, num) )
        num_blanks = len(self.dirList)
        self.curBlankBallotNum.SetLabel("On Style {0} of {1}".format(self.templatenum + 1, num_blanks))

    def addText(self):
        """
        Add the text to the dropdown menus.
        """
        self.text_targets = []

        def changeOptions(x, override=False, fromcombo=False):
            """
            We run this whenever we've changed the title so that we can autopopulate the rest.
            """
            # If override is set to true, it means we should clear it anyways.
            if self.doNotClear and not override:
                return
            
            self.changeCompleted(addone=1)

            if self.focusIsOn == -3:
                self.focusIsOn = -1
                if len(self.text_title.GetValue()) == 1:
                    # HACK this will break with one-character contest titles.
                    self.text_title.SetValue("")
                    self.text_upto.SetValue(1)
                    for i,each in enumerate(self.text_targets):
                        each.Clear()
                        each.SetValue("")
                    return
                

            v = self.text_title.GetValue()

            for k,vv in self.text.items():
                if len(vv) > 0 and v.lower() == vv[0].lower() and len(vv)-1 == len(self.text_targets):
                    # Found it. And there was text corresponding to it.
                    break
            else:
                # This title name hasn't occurred before.
                return

            for i,each in enumerate(self.text_targets):
                each.Clear()
                each.SetValue("")

            self.curtext_matched = vv[1:]
            # Fill in the possible options.
            for i,each in enumerate(self.text_targets):
                # Let them reorder if need be.
                each.AppendItems(vv[1:])
                # And set to the default.
                each.SetValue(vv[1+i])
            self.text_upto.SetValue(self.voteupto[k])


        sz = wx.BoxSizer(wx.VERTICAL)
        self.textarea.SetSizer(sz)
        
        self.contesttitle = wx.StaticText(self.textarea, label="Contest Title", pos=(0,0))
        sz.Add(self.contesttitle)

        number_targets = len(self.groupedtargets[self.templatenum][self.count])

        self.text_title = wx.ComboBox(self.textarea, -1,
                                      choices=list(Set([x[0] for x in self.text.values() if x and len(x)-1 == number_targets])),
                                      style=wx.CB_DROPDOWN, pos=(0,25))
        self.text_title.Bind(wx.EVT_COMBOBOX, lambda x: changeOptions(x, override=True, fromcombo=True))
        self.text_title.Bind(wx.EVT_TEXT, changeOptions)

        sz.Add(self.text_title)

        self.focusIsOn = -1
        def showFocus(where, i=-1):
            # Put a little blue box over where we're entering text
            self.focusIsOn = i
            def doDraw(img):
                mine = np.array(img)
                                      
                l,u,r,d = self.crop[self.currentcontests[self.count]][1]
                #print box
                #dr.rectangle(box, fill=(0,250,0))
                # TODO to get performance, only draw the contest bounding box once
                mine[u:d, l:r] *= .85
                mine[u:d, l:r] += np.array([250, 250, 0])*.15
                if where != None:
                    # Extract the coords, ignore the IDs
                    l,u,r,d = where[2:]
                    mine[u:d, l:r] -= np.array([250, 250, 0])*.15
                    mine[u:d, l:r] *= .85
                    mine[u:d, l:r] += np.array([0, 0, 250])*.15
                    #print todraw
                return mine#Image.blend(mine, img, .85)
            self.changeFocusImage(applyfn=doDraw)

        def enterPushed(it):
            if self.focusIsOn == -3:
                # I've pre-populated the contest with a guess
                wx.CallAfter(self.nextunfilled)
            elif self.focusIsOn == -1:
                # Focus is on the title
                if all([x.GetValue() != '' for x in self.text_targets]):
                    wx.CallAfter(self.nextunfilled)
                else:
                    self.text_targets[0].SetFocus()
            elif self.focusIsOn < len(self.text_targets)-1 and self.focusIsOn != -2:
                # Focus is on a target
                if self.text_targets[self.focusIsOn] != '':
                    self.text_targets[self.focusIsOn+1].SetFocus()
            else:
                if self.text_targets[self.focusIsOn] != '':
                    wx.CallAfter(self.nextunfilled)

        def attempt_prefill(x):
            if self.did_prefill: return
            self.did_prefill = True
            if self.text[self.currentcontests[self.count]] != []: return

            if self.count != 0:
                prev = self.text[self.currentcontests[self.count-1]]
                if prev == []:
                    showFocus(None, -1)
                    return
            else:
                prev = None

            print "PREV", prev

            possible = []
            for template in range(len(self.dirList)):
                order = self.contest_order[template]
                if prev == None:
                    if len(order) == 0: continue
                    maybe = self.text[template,order[0]]
                    if len(maybe)-1 == len(self.text_targets):
                        possible.append((tuple(maybe),self.voteupto[template,order[0]]))
                    continue
                for i in range(1,len(order)):
                    #if self.text[template,order[i-1]] != []:
                    #    print 'itis', self.text[template,order[i-1]]
                    if self.text[template,order[i-1]] == prev:
                        maybe = self.text[template,order[i]]
                        #print 'yes', len(maybe)
                        if len(maybe)-1 == len(self.text_targets):
                            possible.append((tuple(maybe),self.voteupto[template,order[i]]))
            if len(possible) != 0:
                (best,uptoval),ct = max(Counter(map(tuple,possible)).items(), key=lambda x: x[1])
                print "PREFILL WITH", best
                self.text_title.SetValue(best[0])
                self.text_upto.SetValue(uptoval)
                for a,b in zip(best[1:], self.text_targets):
                    b.SetValue(a)
                showFocus(None, -3)
            else:
                showFocus(None, -1)

        self.did_prefill = False
        self.text_title.Bind(wx.EVT_SET_FOCUS, attempt_prefill)

        self.text_title.Bind(wx.EVT_TEXT_ENTER, enterPushed)
        
        if number_targets == 0: 
            self.text_upto = wx.lib.intctrl.IntCtrl(self.textarea, pos=(0,-10000))
            return

        t = wx.StaticText(self.textarea, label="Candidates", pos=(0,70))
        sz.Add(t)
        for i in range(number_targets):
            tt = wx.ComboBox(self.textarea, -1,
                             style=wx.CB_DROPDOWN, pos=(0,95+i*25))
            def c(j):

                def rotate(evt):
                    contestid = self.currentcontests[self.count]
                    if self.is_multibox_contest(contestid):
                        dlg = wx.MessageDialog(self, style=wx.OK,
                                               message="Sorry: Candidate name \
rotation doesn't currently work for multibox contests.")
                        dlg.ShowModal()
                        return
                    pos = self.curtext_matched.index(self.text_targets[j].GetValue())
                    wi = len([name for name in self.curtext_matched if is_writein(name)])
                    if wi == 0:
                        # No writein candidate. Either this is a multibox contest (and
                        # the writein candidate is on the 'next' column), or this contest
                        # simply has no writein candidate.
                        # TODO: This doesn't quite to the right thing for multibox
                        # contests. We need to know the candidate names on the "other"
                        # column to do this properly. We'd also have to modify the
                        # candidate name ordering on the "other" column as well.
                        neworder = self.curtext_matched[pos:] + self.curtext_matched[:pos]
                    else:
                        # Ensure that the writein candidates always stay at the end
                        neworder = self.curtext_matched[pos:-wi]+self.curtext_matched[:pos]
                    for i,l in enumerate(neworder):
                        self.text_targets[i].SetValue(l)

                tt.Bind(wx.EVT_COMBOBOX, rotate)

                tt.Bind(wx.EVT_SET_FOCUS, 
                        lambda x: showFocus(self.groupedtargets[self.templatenum][self.count][j], i=j))
                sz.Add(tt)
            c(i)

            tt.Bind(wx.EVT_TEXT_ENTER, enterPushed)

            # Typing in the top box usually edits the lower stuff
            # We don't want typing to do that if we've modified the text.
            def dontrestore(x): 
                self.doNotClear = True
            tt.Bind(wx.EVT_TEXT, dontrestore)


            self.text_targets.append(tt)

        t = wx.StaticText(self.textarea, label="Vote for up to", pos=(0,25+95+(1+i)*25))
        sz.Add(t)

        self.text_upto = wx.lib.intctrl.IntCtrl(self.textarea, -1,
                                                pos=(0,50+95+(i+1)*25), value=1,
                                                min = 1, max=len(self.text_targets))
        self.text_upto.Bind(wx.EVT_SET_FOCUS, lambda x: showFocus(None))
        def enter_upto(x):
            self.focusIsOn = -2
            enterPushed(x)
        self.text_upto.Bind(wx.EVT_TEXT_ENTER, enterPushed)
        sz.Add(self.text_upto)


    def changeFocusImage(self, move=False, applyfn=None):
        it = self.imgo
        if applyfn != None:
            it = applyfn(it)
        if not move:
            restore = self.imagebox.center, self.imagebox.scale
        self.imagebox.set_image(it)

        coords = self.crop[self.currentcontests[self.count]][1]
        center = ((coords[2]+coords[0])/2, (coords[3]+coords[1])/2)

        percentage_w = float(coords[2]-coords[0])/(self.view_x_size)
        percentage_h = float(coords[3]-coords[1])/(self.view_y_size)
        scale = min(1/percentage_w, 1/percentage_h)
        if not move:
            center, scale = restore
        self.imagebox.set_center(center)
        self.imagebox.set_scale(scale)
        self.imagebox.Refresh()
        

    def nextunfilled(self, x=None):
        # Get the unfilled contests.
        aftertext = [x[0] for x in self.text.items() if x[1] == []]
        # Get their actual order on the screen, not the internal order.
        aftertext = [(t,self.contest_order[t].index(c)) for t,c in aftertext]
        # Remove the ones before the current contest.
        aftertext = [x for x in aftertext if x > (self.templatenum, self.count)]
        # Pick the first.
        if len(aftertext) == 0: return

        temp,cont = min(aftertext)
        if temp != self.templatenum:
            print 'skip to', temp-self.templatenum
            self.nexttemplate(temp-self.templatenum)
        
        self.doadd(cont-self.count)

    def doadd(self, ctby, dosave=True):
        """
        Set up everything for a given contest.
        ctby is how many contests to skip by.
        It's usually 1 or -1 (forward/backward).
        Sometimes it's 0 to show the contest for the first time.
        """

        if self.count+ctby >= len(self.currentcontests):
            self.nexttemplate(1)
            return
        if self.count+ctby < 0:
            self.nexttemplate(-1)
            return

        self.doNotClear = False

        if dosave:
            # We don't want to save when we're moving to a different
            #  ballot image. We've already done that in nexttemplate.
            self.saveText()

        self.count += ctby

        self.changeCompleted()

        self.textarea.DestroyChildren()

        self.updateTemplate()

        self.changeFocusImage(move=True)
        
        self.addText()

        self.restoreText()
        
        self.text_title.SetFocus()

        self.Fit()

def is_writein(name):
    """ Returns True if the candidate name is a write-in name.
    We define a write in name if it starts with the phrase 'write', i.e.:
        write in
        write-in
        writein
        writein1, writein2, etc.
    """
    name = name.lower()
    return name.startswith("write")
