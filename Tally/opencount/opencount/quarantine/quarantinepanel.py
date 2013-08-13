import wx
import wx.lib.scrolledpanel
from util import ImageManipulate
from PIL import Image
import csv
import os
from collections import defaultdict

try:
    import cPickle as pickle
except:
    import pickle

from os.path import join as pathjoin

class QuarantinePanel(wx.Panel):
    firstTime = True

    def __init__(self, parent, *args, **kwargs):
        wx.Panel.__init__(self, parent, -1, *args, **kwargs)
        self.parent = parent
        self.quarantinepanel = None

    def start(self, proj, sz):
        self.proj = proj
        if not self.firstTime: return
        self.firstTime = False

        qballotids = get_quarantined_ballots(proj)
        top = TopPanel(self)
        self.quarantinepanel = MainPanel(self, qballotids, self.proj, sz)
        top.start(self.quarantinepanel)

        sizer = wx.BoxSizer(wx.VERTICAL)
        sizer.Add(top, proportion=1, flag=wx.ALL | wx.EXPAND, border=5)
        sizer.Add(self.quarantinepanel, proportion=10, flag=wx.EXPAND)
        self.SetSizer(sizer)
        self.Fit()
        self.Refresh()

    def stop(self):
        if self.quarantinepanel:
            # Funny thing: If there are no quarantined attributes, then
            # the page change can happen before self.quarantinepanel gets set.
            self.quarantinepanel.save()
            self.proj.removeCloseEvent(self.quarantinepanel.save)

class MainPanel(wx.Panel):
    def __init__(self, parent, qballotids, proj, sz, *args, **kwargs):
        wx.Panel.__init__(self, parent, -1, *args, **kwargs)

        self.parent = parent
        self.proj = proj
        self.qballotids = qballotids
        #print 'QBALLOTS {}'.format(qballotids)
        self.img2bal = pickle.load(open(proj.image_to_ballot, 'rb'))
        bal2img = pickle.load(open(self.proj.ballot_to_images, 'rb'))
        img2page = pickle.load(open(pathjoin(self.proj.projdir_path, self.proj.image_to_page), 'rb'))        
        self.bal2group = pickle.load(open(pathjoin(self.proj.projdir_path, self.proj.ballot_to_group), 'rb'))
        if os.path.exists(pathjoin(self.proj.projdir_path, self.proj.partition_attrmap)):
            self.part2attrs = pickle.load(open(pathjoin(self.proj.projdir_path, self.proj.partition_attrmap), 'rb'))

        # compute contests for each group ID to display contests for decoded ballots
        group_exmpls = pickle.load(open(pathjoin(self.proj.projdir_path, self.proj.group_exmpls), 'rb'))
        groupID_imgpaths = [(x[0],sorted(bal2img[x[1][0]], key=lambda imP: img2page[imP])) for x in group_exmpls.items()]
        rep_paths = [path for id_paths in groupID_imgpaths for path in id_paths[1]]
        img_contest_dict = defaultdict(list)
        for line in csv.reader(open(self.proj.contest_id)):
            if line[0] in rep_paths:
                img_contest_dict[line[0]].append((line[1], line[2]))
        self.group2contests = {}
        for groupID, imgpaths in groupID_imgpaths:
            self.group2contests[groupID] = []
            for imgpath in imgpaths:
                self.group2contests[groupID].append([int(x[1]) for x in sorted(img_contest_dict[imgpath])])

        self.qfiles          = []    # [quarantined_filepath1, ...]
        self.data            = []    # [[contestID, True, False, ...], ...]
        self.discardlist     = []    # [False, True, ...]
        self.attributes      = []    # ?

        self.curballot       = 0     # index in self.qfiles
        self.labeltext       = {}    # {contestid: [cand1, cand2, ...], ...}
        self.sizer_checklist = {}    # {contest_name: (sizer, checklist)}

        # adjustable parameters
        self.contest_pane_width  = 200
        self.contest_pane_height = sz[1]-400
        self.attr_pane_height    = 400
        self.scroll_area_width   = self.contest_pane_width + 150

        # aggregate all quarantined imagepaths
        self.imgpath2page = {}
        for ballotid in qballotids:
            imgpaths = bal2img[ballotid]
            try:
                imgpaths = sorted(imgpaths, key=lambda imP: img2page[imP])
            except KeyError as e:
                # imgpaths won't be in img2page if BALLOTID was quarantined
                # during decoding (since img2page is built on decoding). So,
                # we don't know the proper order - at worst, this means that
                # the user will have to manually correct the auto-loaded
                # contests if it gets the front/back wrong, which is fine.
                pass
            for i,imgpath in enumerate(imgpaths):
                self.imgpath2page[imgpath] = i
            self.qfiles.extend(imgpaths)
        self.qfiles = sorted(list(set(self.qfiles)))

        # build list of attributes
        self.ballot_attributes = self.load_grouping()
        #print 'attributes {}'.format(self.ballot_attributes)

        # make list of contests and candidates
        temp_contest_dict = {}
        for line in csv.reader(open(self.proj.contest_text)):
            if len(line) < 2: break
            temp_contest_dict[int(line[0])] = line[2:]
        self.labeltext = [x[1] for x in sorted(temp_contest_dict.items())]
        self.labeltext_alphabetical = sorted(self.labeltext)
        self.glob2sorted_index = []
        for x in self.labeltext:
            self.glob2sorted_index.append(self.labeltext_alphabetical.index(x))
        self.title_names = [x[0] for x in self.labeltext_alphabetical]
        #print 'glob {}'.format([x[0] for x in self.labeltext])
        #print 'glob2sorted {}'.format(self.glob2sorted_index)
        #print 'labeltext {}'.format(self.labeltext)
        #print 'ltalpha {}'.format(self.labeltext_alphabetical)
        #print 'sorted_titles {}'.format(self.title_names)

        # load saved information
        if os.path.exists(self.proj.quarantine_internal):
            self.data, self.discardlist, self.attributes = pickle.load(open(self.proj.quarantine_internal))

        # create left pane for image
        self.image_width = max(sz[0]/2, 400)
        self.image_height = max(sz[1]-200, 500)
        self.imagebox = ImageManipulate(self, size=(self.image_width,self.image_height))
        szh_zoom = wx.BoxSizer(wx.HORIZONTAL)
        zoomin = wx.Button(self, label="Zoom In")
        zoomout = wx.Button(self, label="Zoom Out")
        zoomin.Bind(wx.EVT_BUTTON, lambda x: self.imagebox.zoomin())
        zoomout.Bind(wx.EVT_BUTTON, lambda x: self.imagebox.zoomout())
        szh_zoom.Add(zoomin)
        szh_zoom.Add(zoomout)
        szv_rightpane = wx.BoxSizer(wx.VERTICAL)
        szv_rightpane.Add(szh_zoom, border=10, flag=wx.BOTTOM)
        szv_rightpane.Add(self.imagebox)
        self.imagebox.zoomin()

        # create pane for contests
        self.contest_dropdown = wx.Choice(self, size=(self.contest_pane_width, 30), choices=self.title_names)
        add_btn = wx.Button(self, id=wx.ID_ADD)
        add_btn.Bind(wx.EVT_BUTTON, self.add_contest_handler)
        clear_btn = wx.Button(self, id=wx.ID_CLEAR)
        clear_btn.Bind(wx.EVT_BUTTON, self.clear_contests)
        szh_select_contest = wx.BoxSizer(wx.HORIZONTAL)
        szh_select_contest.Add(self.contest_dropdown)
        szh_select_contest.Add(add_btn, border=10, flag=wx.LEFT)
        szh_select_contest.Add(clear_btn, border=10, flag=wx.LEFT)
        self.szv_add_contest = wx.BoxSizer(wx.VERTICAL)
        self.szv_add_contest.Add(self.create_title(self, 'Select Contest'), border=5, flag=wx.BOTTOM)
        self.szv_add_contest.Add(szh_select_contest, border=15, flag=wx.BOTTOM)

        self.contest_panel = wx.lib.scrolledpanel.ScrolledPanel(self, size=(self.scroll_area_width, self.contest_pane_height))
        self.contest_panel.SetAutoLayout(True)
        self.contest_panel.SetupScrolling(False, True)
        self.szv_contests = wx.BoxSizer(wx.VERTICAL)
        self.contest_panel.SetSizer(self.szv_contests)

        self.attribute_panel = wx.lib.scrolledpanel.ScrolledPanel(self, size=(self.scroll_area_width, self.contest_pane_height))
        self.attribute_panel.SetAutoLayout(True)
        self.attribute_panel.SetupScrolling(False, True)
        self.attribute_area = wx.BoxSizer(wx.VERTICAL)
        self.attribute_panel.SetSizer(self.attribute_area)

        szv_leftpane = wx.BoxSizer(wx.VERTICAL)
        self.discard = wx.CheckBox(self, label="Discard ballot")
        self.discard.Bind(wx.EVT_CHECKBOX, self.discard_handler)
        szv_leftpane.Add(self.discard)
        szv_leftpane.Add(self.szv_add_contest, border=10, flag=wx.TOP)
        szv_leftpane.Add(self.contest_panel) #, proportion=1, flag=wx.ALL | wx.EXPAND, border=5)
        szv_leftpane.Add(self.attribute_panel, border=20, flag=wx.TOP) # proportion=1, flag=wx.ALL | wx.EXPAND, border=5)

        # create main panel by joining left and right panes
        szh_main = wx.BoxSizer(wx.HORIZONTAL)
        szh_main.Add(szv_leftpane, border=25, flag=wx.LEFT)
        szh_main.Add(szv_rightpane, border=25, flag=wx.LEFT)
        self.SetSizer(szh_main)

        self.attributes_text = []
        if self.ballot_attributes:
            if self.ballot_attributes.get('header'):
                self.attribute_area.Add(wx.StaticText(self.attribute_panel, -1, label="Enter the ballot attributes below."))
                for title in self.ballot_attributes['header'][1:]:
                    sz = wx.BoxSizer(wx.HORIZONTAL)
                    attr = wx.TextCtrl(self.attribute_panel, -1)
                    sz.Add(wx.StaticText(self.attribute_panel, -1, label=title))
                    sz.Add(attr)
                    self.attributes_text.append(attr)
                    self.attribute_area.Add(sz)

        # move on to next step if no quarantined ballots
        if not self.qfiles:
            dlg = wx.MessageDialog(self, message="OpenCount did not \
                quarantine any voted ballot images - in fact, it seemed to be able \
                to process all voted ballots just fine. Press 'Ok' to proceed to \
                the next step.", style=wx.OK)
            self.Disable()
            dlg.ShowModal()
            self.Enable()
            self.save()
            # Change pages to the next step
            notebook = self.parent.parent
            oldpage = notebook.GetSelection()
            notebook.ChangeSelection(oldpage + 1)
            notebook.SendPageChangedEvent(oldpage, oldpage + 1)
            return

        self.proj.addCloseEvent(self.save)
        self.show_ballot(0, True)

    def create_title(self, parent, text):
        ''' Create a bold StaticText object '''
        st = wx.StaticText(parent, label=text)
        font = st.GetFont()
        font.SetWeight(wx.BOLD)
        st.SetFont(font)
        return st

    def add_contest_handler(self, event):
        ''' Handler to add contest selected in dropdown '''
        index = self.contest_dropdown.GetSelection()
        if index == -1: return
        self.add_contest(index)

    def add_contest(self, index):
        ''' Adds the contest at index on the dropdown '''
        contest = self.labeltext_alphabetical[index]
        contest_name = contest[0]
        # check if contest already added
        if (contest_name,index) in self.sizer_checklist: return
        candlist = wx.CheckListBox(self.contest_panel, size=(self.contest_pane_width, (len(contest) - 1) * 24), choices=contest[1:])
        btn_rm = wx.Button(self.contest_panel, id=wx.ID_REMOVE, name=contest_name+'$'+str(index))
        btn_rm.Bind(wx.EVT_BUTTON, self.remove_contest_handler)
        szv = wx.BoxSizer(wx.VERTICAL)
        szh = wx.BoxSizer(wx.HORIZONTAL)
        szv.Add(self.create_title(self.contest_panel, contest_name), border=5, flag=wx.BOTTOM)
        szh.Add(candlist)
        szh.Add(btn_rm, border=10, flag=wx.ALL | wx.ALIGN_CENTER_VERTICAL)
        szv.Add(szh)
        self.szv_contests.InsertSizer(0, szv, border=10, flag=wx.BOTTOM)
        self.contest_panel.Fit()
        self.contest_panel.Refresh()
        self.sizer_checklist[(contest_name,index)] = (szv, candlist)
        self.contest_order.append(index)

    def remove_contest_handler(self, event):
        ''' Remove contest associated with button that triggered the event '''
        btn = event.GetEventObject()
        contest_name,index = btn.GetName().split('$')
        self.remove_contest(contest_name, int(index))

    def remove_contest(self, contest_name, index):
        ''' Remove contest associated with button that triggered the event '''
        contest_sizer = self.sizer_checklist[(contest_name,index)][0]
        self.szv_contests.Hide(contest_sizer)
        self.szv_contests.Remove(contest_sizer)
        self.contest_panel.Fit()
        self.contest_panel.Refresh()
        del self.sizer_checklist[(contest_name,index)]
        self.contest_order.remove(index)

    def clear_contests(self, event):
        ''' Clear all contests '''
        for contest_name,index in [x[0] for x in self.sizer_checklist.items()]:
            self.remove_contest(contest_name,index)

    def discard_handler(self, event):
        checkbox = event.GetEventObject()
        self.discard_update(checkbox.GetValue())

    def discard_update(self, checked):
        ''' Hide ability to add contests if discarding ballot '''
        for i in range(len(self.szv_add_contest.GetChildren())):
            if checked: self.szv_add_contest.Hide(i)
            else: self.szv_add_contest.Show(i)
        self.szv_add_contest.Layout()
        if checked: self.clear_contests(None)

    def show_ballot(self, n, firsttime=False):
        ''' Show ballot n in the main panel '''
        # save data if any
        if self.curballot < len(self.data) and not firsttime:
            self.save_contest_data()
            self.attributes[self.curballot] = [x.GetValue() for x in self.attributes_text]

        # create entries for new ballot
        while n >= len(self.data):
            self.data.append([])
            self.discardlist.append(False)
            self.attributes.append([])

        # update and clean up
        self.curballot = n
        bID = self.img2bal[self.qfiles[n]]
        for child in self.contest_panel.GetChildren(): child.Destroy()
        self.szv_contests.Clear()
        self.sizer_checklist = {}
        self.contest_order = []

        # load image
        f = Image.open(self.qfiles[n])
        self.imagebox.set_image(f)
        self.imagebox.set_scale(0.4)
        self.imagebox.Refresh()

        # load contest data
        for contest_data in self.data[n]:
            contest_id = contest_data[0]
            contest_info = self.labeltext[contest_id]
            contest_name = contest_info[0]
            alpha_id = self.glob2sorted_index[contest_id]
            self.add_contest(alpha_id)
            checklist = self.sizer_checklist[(contest_name,alpha_id)][1]
            selected_candidates = []
            for i, voted in enumerate(contest_data[1:]):
                if voted: selected_candidates.append(self.labeltext_alphabetical[alpha_id][1:][i])
            checklist.SetCheckedStrings(selected_candidates)
        if not self.data[n] and bID in self.bal2group:
            group = self.bal2group[bID]
            toAdd = []
            for contestID in self.group2contests[group][self.imgpath2page[self.qfiles[n]]]:
                new_index = self.glob2sorted_index[contestID]
                toAdd.insert(0, new_index)
            for index in toAdd:
                self.add_contest(index)
        self.contest_panel.Fit()
        self.contest_panel.Refresh()
        #print 'contest_order {}'.format(self.contest_order)

        # load attribute data
        attrs = []
        if self.attributes[self.curballot] != []:
            attrs = self.attributes[n]
        elif self.ballot_attributes:
            if self.qfiles[self.curballot] in self.ballot_attributes:
                attrs = self.ballot_attributes[self.qfiles[self.curballot]][1:]
            else:
                attrs = [''] * (len(self.ballot_attributes['header']) - 1)

        #print self.curballot, self.ballot_attributes
        #print self.attributes[self.curballot]
        #print 'here {}, {}'.format(self.attributes_text, attrs)
        for inp, dat in zip(self.attributes_text, attrs): inp.SetValue(dat)

        discarded = self.discardlist[n]
        self.discard.SetValue(discarded)
        self.discard_update(discarded)
        self.Fit()
        self.Refresh()

    def save(self):
        ''' Save and dump all data to disk '''
        self.save_contest_data()
        pickle.dump((self.data, self.discardlist, self.attributes), open(self.proj.quarantine_internal, "w"))
        out = open(self.proj.quarantine_res, "w")
        outattr = csv.writer(open(self.proj.quarantine_attributes, "w"))
        for bpath, ballot, drop, attr in zip(self.qfiles, self.data, self.discardlist, self.attributes):
            if drop: continue
            out.write(bpath + ",")
            outattr.writerow([bpath] + attr)
            for contest in ballot:
                out.write(str(contest[0]) + ",")
                for each in contest[1:]:
                    # Write T/F for this contest
                    out.write(str(each)[0])
                out.write(",")
            out.write("\n")
        out.close()

    def save_contest_data(self):
        ''' Save contest data for ballot currently opened '''
        if not self.qfiles:
            print "== quarantine save_contest_data: No quarantined \
                    ballot images exist, so, no need to save contest data."
            return
        new_collected = []
        for (name,index),sizer_checklist in self.sizer_checklist.items():
            contest_info = self.labeltext_alphabetical[index]
            contestid = self.labeltext.index(contest_info)
            checked = sizer_checklist[1].GetChecked()
            votes = [contestid]
            for i in range(len(contest_info) - 1):
                voted = True if i in checked else False
                votes.append(voted)
            new_collected.append(votes)
        ballot_global_ids_sorted = [self.glob2sorted_index.index(x) for x in self.contest_order]
        new_collected.sort(key=lambda x: ballot_global_ids_sorted.index(x[0]))
        self.data[self.curballot] = new_collected

        self.discardlist[self.curballot] = self.discard.GetValue()
        for i, txtinput in enumerate(self.attributes_text):
            if i < len(self.attributes[self.curballot]):
                self.attributes[self.curballot][i] = txtinput.GetValue()
            else:
                self.attributes[self.curballot].append(txtinput.GetValue())

    def load_grouping(self):
        ''' Load attribute groups'''
        if not os.path.exists(self.proj.grouping_results):
            return None

        bal2imgs = pickle.load(open(self.proj.ballot_to_images, 'rb'))
        img2page = pickle.load(open(pathjoin(self.proj.projdir_path,
                                             self.proj.image_to_page), 'rb'))

        c_t = {}
        for line in csv.reader(open(self.proj.grouping_results)):
            if len(line) < 2: continue
            if line[0] == 'ballotid':
                attrtypes = line[1:]
                attrtypes = attrtypes[:-1]  # ignore partitionID (always at end)
                c_t['header'] = attrtypes
            elif line[0] in self.qfiles:
                ballotid = int(line[0])
                imgpaths = bal2imgs[ballotid]
                imgpaths_ordered = sorted(imgpaths, key=lambda imP: img2page[imP])
                attrvals = line[1:]
                attrvals = attrvals[:-1]  # ignore partitionID (always at end)
                c_t[imgpaths_ordered[0]] = attrvals
        return c_t

class TopPanel(wx.Panel):
    def __init__(self, parent):
        wx.Panel.__init__(self, parent, -1)

    def start(self, main):

        curnum = wx.StaticText(self, -1)
        curnum.SetLabel("1 of " + str(len(main.qfiles)))

        path = wx.StaticText(self, -1)
        if len(main.qfiles) > 0:
            path.SetLabel("Path: " + main.qfiles[0])

        def do(x, jumpto=None):
            if jumpto != None:
                v = jumpto
            else:
                v = int(curnum.GetLabel().split(" ")[0]) + x
            if 0 < v <= len(main.qfiles):
                curnum.SetLabel(str(v) + " of " + str(len(main.qfiles)))
                path.SetLabel("Path: " + str(main.qfiles[v - 1]))
                main.show_ballot(v - 1)

        prev = wx.Button(self, -1, label="Previous Ballot")
        prev.Bind(wx.EVT_BUTTON, lambda x: do(-1))
        nxt = wx.Button(self, -1, label="Next Ballot")
        nxt.Bind(wx.EVT_BUTTON, lambda x: do(1))

        def onbutton_jumpto(evt):
            dlg = wx.TextEntryDialog(self, message="Enter the ballot index (integer):",
                                     style=wx.OK | wx.CANCEL)
            status = dlg.ShowModal()
            if status == wx.ID_CANCEL:
                return
            try:
                idx = int(dlg.GetValue())
                do(None, jumpto=idx)
            except ValueError:
                pass

        btn_jumpto = wx.Button(self, label="Jump to...")
        btn_jumpto.Bind(wx.EVT_BUTTON, onbutton_jumpto)

        mainsizer = wx.BoxSizer(wx.VERTICAL)
        sizer = wx.BoxSizer(wx.HORIZONTAL)
        sizer.Add(prev)
        sizer.Add(curnum, border=10, flag=wx.LEFT|wx.RIGHT)
        sizer.Add(nxt)
        sizer.AddMany([((10,0),), (btn_jumpto)])
        mainsizer.Add(sizer)
        mainsizer.Add(path)

        self.SetSizer(mainsizer)

        self.Fit()
        self.Refresh()

def get_quarantined_ballots(proj):
    qballotids = []
    partition_qpath = pathjoin(proj.projdir_path, proj.partition_quarantined)
    if os.path.exists(partition_qpath):
        qballotids.extend(pickle.load(open(partition_qpath, 'rb')))
    grouping_qpath = pathjoin(proj.projdir_path, proj.grouping_quarantined)
    if os.path.exists(grouping_qpath):
        # list GROUPING_QUARANTINED: [int ballotID_i, ...]
        qballotids.extend(pickle.load(open(grouping_qpath, 'rb')))
    if os.path.exists(pathjoin(proj.projdir_path, 'quarantinedbals_seltargets.p')):
        qballotids.extend(list(pickle.load(open(pathjoin(proj.projdir_path, 'quarantinedbals_seltargets.p')))))
    targetextract_qpath = pathjoin(proj.projdir_path, proj.targetextract_quarantined)
    if os.path.exists(targetextract_qpath):
        qballotids.extend(pickle.load(open(targetextract_qpath, 'rb')))
    if os.path.exists(proj.quarantined):
        lines = open(proj.quarantined, 'r').read().split("\n")
        lines = [int(l) for l in lines if l != '']
        qballotids.extend(lines)
    if os.path.exists(proj.quarantined_manual):
        lines = open(proj.quarantined_manual, 'r').read().split("\n")
        lines = [int(l) for l in lines if l != '']
        qballotids.extend(lines)
    return list(set(qballotids))

def get_discarded_ballots(proj):
    discarded_balids = []
    if os.path.exists(pathjoin(proj.projdir_path, proj.partition_discarded)):
        discarded_balids.extend(pickle.load(open(pathjoin(proj.projdir_path,
                                                          proj.partition_discarded), 'rb')))
    if os.path.exists(proj.quarantine_internal):
        # Bit hacky: Peer into QuarantinePanel's internal state
        bal2imgs = pickle.load(open(proj.ballot_to_images, 'rb'))
        img2bal = pickle.load(open(proj.image_to_ballot, 'rb'))
        # Recreate the qfiles data structure...
        qballotids = list(sorted(get_quarantined_ballots(proj)))
        qfiles = []
        for qballotid in qballotids:
            qfiles.extend(bal2imgs[qballotid])
        qfiles = sorted(list(set(qfiles)))
        data, discardlist, attributes = pickle.load(open(proj.quarantine_internal, 'rb'))
        for i, isDiscard in enumerate(discardlist):
            if isDiscard:
                imgpath = qfiles[i]
                discarded_balids.append(img2bal[imgpath])

    return list(set(discarded_balids))
