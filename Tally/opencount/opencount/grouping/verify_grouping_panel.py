import os, sys, pdb, csv, re
try:
    import cPickle as pickle
except:
    import pickle

from os.path import join as pathjoin

import wx

from verify_overlays_new import VerifyOrFlagOverlaysPanel, VerifyOrFlagOverlaysFooter, VerifyOrFlagOverlays, VerifyOverlaysMultCats
import digit_group_new, cust_attrs
sys.path.append('..')
import specify_voting_targets.util_gui as util_gui
import config

class VerifyGroupingMainPanel(wx.Panel):
    # Number of exemplars to grab for each group
    NUM_EXMPLS = 5

    def __init__(self, parent, *args, **kwargs):
        wx.Panel.__init__(self, parent, *args, **kwargs)
        
        self.proj = None
        self.stateP = None

        self.imgpath_groups = None
        self.group_exemplars = None
        self.bbs_map = None
        self.rlist_map = None

        # VERIFY_RESULTS: maps {attrtype: {attrval: [imgpath_i, ...]}}
        self.verify_results = None

        self.init_ui()

    def init_ui(self):
        self.verify_panel = VerifyBallotOverlaysMultCats(self)
        
        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.sizer.Add(self.verify_panel, proportion=1, flag=wx.EXPAND)
        self.SetSizer(self.sizer)

        self.Layout()

    def start(self, proj, stateP):
        self.proj = proj
        self.proj.addCloseEvent(self.save_session)
        self.stateP = stateP

        if config.TIMER:
            config.TIMER.start_task("VerifyGrouping_Verify_H")

        if not self.restore_session():
            self.group_exemplars = get_group_exemplars(proj)
            self.imgpath_groups = create_groups(proj)
            self.rlist_map = get_rlist_map(proj)

        if os.path.exists(pathjoin(self.proj.projdir_path,
                                   self.proj.imgpatch2imgpath)):
            patch2imgpath = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                      self.proj.imgpatch2imgpath), 'rb'))
        else:
            patch2imgpath = {}
        if os.path.exists(pathjoin(self.proj.projdir_path,
                                   self.proj.digpatch2imgpath)):
            digpatch2imgpath = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                         self.proj.digpatch2imgpath), 'rb'))
        else:
            digpatch2imgpath = {}

        verifyoverlays_stateP = pathjoin(proj.projdir_path, '_state_verifyoverlays.p')

        if self.imgpath_groups:
            self.verify_panel.start(self.proj, self.imgpath_groups, self.group_exemplars, 
                                    patch2imgpath, digpatch2imgpath,
                                    ondone=self.on_verify_done, do_align=False, 
                                    verifypanelClass=VerifyBallotAttributesPanel)
        else:
            print "(VerifyGrouping): No img/digit-based attrs required to verify."
            wx.MessageDialog(self, message="It is not necessary to verify any groups. Please move onto the \
next step.", style=wx.OK).ShowModal()
            
        self.Layout()

    def stop(self):
        if not self.proj:
            return
        self.save_session()
        self.proj.removeCloseEvent(self.save_session)
        self.export_results()

    def restore_session(self):
        try:
            state = pickle.load(open(self.stateP, 'rb'))
            self.imgpath_groups = state['imgpath_groups']
            self.group_exemplars = state['group_exemplars']
            self.rlist_map = state['rlist_map']
            self.bbs_map = state['bbs_map']
        except:
            return False
        return True
    def save_session(self):
        state = {'imgpath_groups': self.imgpath_groups,
                 'group_exemplars': self.group_exemplars,
                 'rlist_map': self.rlist_map,
                 'bbs_map': self.bbs_map}
        pickle.dump(state, open(self.stateP, 'wb'), pickle.HIGHEST_PROTOCOL)
        self.verify_panel.save_session()

    def export_results(self):
        """ Establishes the ballot -> group relationship, by exporting
        the BALLOT_TO_GROUP dict:
            {int ballotID: int groupID}
        and GROUP_TO_BALLOTS:
            {int groupID: [int ballotID_i, ...]}
        and GROUP_INFOMAP:
            {int groupID: {str key: val}}
        and GROUP_EXMPLS:
            {int groupID: [int ballotID_i, ...]}
        """
        if not self.verify_results:
            print "(VerifyGrouping): self.verify_results is empty, implies no non-tabulationonly img/digit-based attrs"
            self.verify_results = {}

        b2g = {}
        g2b = {}
        group_infomap = {}
        group_exmpls = {}

        b2imgs = pickle.load(open(self.proj.ballot_to_images, 'rb'))
        img2b = pickle.load(open(self.proj.image_to_ballot, 'rb'))

        partitions_map = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                   self.proj.partitions_map), 'rb'))
        partitions_invmap = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                      self.proj.partitions_invmap), 'rb'))
        """
        dict attrprops: {str ATTRMODE: dict PROPS}
            where ATTRMODE in ('DIGITBASED', 'IMGBASED', 'CUSTATTR')
            and PROPS has keys: 'attrtype', 'x1','y1','x2','y2', 'is_tabulationonly',
                                'side', 'grp_per_partition', 'num_digits'
        """                   
        attrprops = pickle.load(open(pathjoin(self.proj.projdir_path, 
                                              self.proj.attrprops), 'rb'))
        # dict part2attrs: {int partitionid: [(imgpath,x1,y1,w,h,attrtype,attrval,side,isdigitbased,istabonly),...]}
        part2attrs = pickle.load(open(pathjoin(self.proj.projdir_path,
                                               self.proj.partition_attrmap), 'rb'))
        
        attrs = pickle.load(open(self.proj.ballot_attributesfile, 'rb'))
        attrmap = {} # maps {str attrtype: dict attr_marsh}
        for attr in attrs:
            attrmap['_'.join(sorted(attr['attrs']))] = attr

        def is_part_consistent(attrtype):
            return attrmap[attrtype]['grp_per_partition']
        if not attrprops['DIGITBASED']:
            part2digitattrval = {}
        else:
            # dict DIGITATTRVALS_BLANKS: {str imgpath: {str digattrtype: (str digitval, bb, side)}}
            digitattrvals_blanks = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                             self.proj.digitattrvals_blanks)))
            part2digitattrval = {} # maps {int partitionid: str digitval}
            for imgpath, digittypemap in digitattrvals_blanks.iteritems():
                balid = img2b[imgpath]
                partitionid = partitions_invmap[balid]
                for digitattrtype, (digitval, bb, side) in digittypemap.iteritems():
                    part2digitattrval[partitionid] = digitval
        def get_digit_val(partitionid):
            return part2digitattrval[partitionid]

        # 1.) First, mark each ballot with its attribute properties
        ballot_attrvals = {} # maps {int ballotID: {attrtype: attrval}}
        # Prepopulate this with each ballots partition id
        for partitionid, ballotids in partitions_map.iteritems():
            for ballotid in ballotids:
                ballot_attrvals[ballotid] = {'pid': partitionid}
            
        # Note: For an attr, if groupingmode was PER_PARTITION, then
        # grouping was not done -- use the per-partition labeling.
        for partitionid, attrtupls in part2attrs.iteritems():
            for (_,_,_,_,_, attrtype, attrval, _,isdigitbased,istabonly) in attrtupls:
                if is_part_consistent(attrtype):
                    ballotids = partitions_map[partitionid]
                    if isdigitbased:
                        attrval = get_digit_val(partitionid)
                    for balid in ballotids:
                        ballot_attrvals.setdefault(balid, {})[attrtype] = attrval
                    
        for attrtype, attrvaldict in self.verify_results.iteritems():
            if is_part_consistent(attrtype):
                # Grouping isn't done for partition-consistent attrs
                continue
            for attrval, imgpaths in attrvaldict.iteritems():
                for imgpath in imgpaths:
                    ballotid = img2b[imgpath]
                    ballot_attrvals.setdefault(ballotid, {})[attrtype] = attrval

        # 1.b.) Add CUSTOM_ATTRIBUTE mapping
        flag_ssAttrExists = False
        ss_dicts = {} # maps {str attrtype: dict ss_dict}
        for attrtype, cattrprops in attrprops.get('CUSTATTR', {}).iteritems():
            if cattrprops['type'] == cust_attrs.TYPE_SPREADSHEET:
                flag_ssAttrExists = True
                ssdict = ss_dicts.get(attrtype, None)
                if ssdict == None:
                    ss_dicts[attrtype] = read_sscustattr(cattrprops['sspath'])
                    ssdict = ss_dicts[attrtype]
                for ballotid, ballotprops in ballot_attrvals.iteritems():
                    inval = ballotprops[cattrprops['attrin']]
                    ballotprops[attrtype] = ssdict[inval]
            elif cattrprops['type'] == cust_attrs.TYPE_FILENAME:
                for ballotid, ballotprops in ballot_attrvals.iteritems():
                    # Arbitrarily select the first image path...good?
                    imgname = b2imgs[ballotid][0]
                    matches = re.search(cattrprops['filename_regex'], imgname)
                    outval = matches.groups()[0]
                    ballotprops[attrtype] = outval
        # 2.) Create each group, based on the unique ballot property values
        group_idx_map = {} # maps {((attrtype,attrval), ...): int groupIdx}
        group_cnt = 0

        if os.path.exists(pathjoin(self.proj.projdir_path, self.proj.ballot_to_group)):
            b2g_old = pickle.load(open(pathjoin(self.proj.projdir_path, self.proj.ballot_to_group)))
        else:
            b2g_old = None

        def all_attrs_tabulationonly():
            """ Returns True if all attributes are tabulation-only. """
            # list ATTRS: [dict attrbox_marsh, ...]
            for attrdict in attrs:
                if not attrdict['is_tabulationonly']:
                    return False
            return True

        img2page = pickle.load(open(pathjoin(self.proj.projdir_path,
                                             self.proj.image_to_page), 'rb'))
        img2info = pickle.load(open(pathjoin(self.proj.projdir_path, self.proj.imginfo_map), 'rb'))
        def getpagenums(balid):
            """ Returns the page numbers present for this ballot. """
            imgpaths = b2imgs[balid]
            return tuple(sorted([img2page[imP] for imP in imgpaths]))

        def get_barcode_props(balid):
            """ If the current Vendor can provide additional grouping
            criterion (say, from the barcodes), then this will return them.
            """
            imgpaths = b2imgs[balid]
            info = img2info[imgpaths[0]]
            propnames = self.proj.vendor_obj.get_grouping_propnames()
            out_dict = {} # maps {str propname: str propval}
            for propname in propnames:
                out_dict[propname] = info[propname]
            return out_dict
            
        for ballotid, ballotprops in ballot_attrvals.iteritems():
            # 2.a.) Filter out any 'is_tabulationonly' attrtypes
            ballotprops_grp = {} # maps {attrtype: attrval}
            numpages = len(b2imgs[ballotid]) # always also group by # of pages!
            for ballotattrtype, ballotattrval in ballotprops.iteritems():
                if ballotattrtype == 'pid' and not flag_ssAttrExists:
                    # Always add the partition id as a grouping criterion.
                    # But, if a SpreadSheet custAttr exists, then we assume that
                    # the partitionid will NOT be used for grouping purposes.
                    ballotprops_grp[ballotattrtype] = ballotattrval
                    continue
                for attrmode, attrdicts in attrprops.iteritems():
                    for attrtype, attrpropdict in attrdicts.iteritems():
                        if attrtype == ballotattrtype and not attrpropdict['is_tabulationonly']:
                            ballotprops_grp[ballotattrtype] = ballotattrval
            # 2.b.) Also add in any additional grouping criterion that
            # the Vendor may provide (i.e. from the barcodes).
            for propname, propval in get_barcode_props(ballotid).iteritems():
                if propname not in ballotprops_grp:
                    ballotprops_grp[propname] = propval

            ordered_props = tuple(sorted(ballotprops_grp.items(), key=lambda t: t[0])) + (numpages,)
            if flag_ssAttrExists:
                # For var-num-page elections, there's a possibility
                # that ballots may be missing sides, i.e. ballot A has
                # pages [0, 1] and ballot B has pages [1, 2]. Even if A and B
                # both have the same ballot attributes, they should still
                # /not/ be grouped together. So, add a new criterion to the
                # ORDERED_PROPS group tag.
                ordered_props += (getpagenums(ballotid),)
            if all_attrs_tabulationonly() and b2g_old != None and ballotid in b2g_old:
                # Use the prior group indexing scheme!
                # NOTE: This code will NOT gracefully handle the case where
                #       some ballots are found in B2G_OLD, and others are not
                #       found in B2G_OLD. The latter ballots may get assigned
                #       groupids that were assigned to the former ballots - 
                #       however, this case should only happen if more ballots
                #       were added since the last grouping (at which case
                #       the project should have just been started over)
                group_idx = b2g_old[ballotid]
                group_idx_map[ordered_props] = group_idx
            else:
                group_idx = group_idx_map.get(ordered_props, None)
                if group_idx == None:
                    group_idx = group_cnt
                    group_idx_map[ordered_props] = group_idx
                    group_cnt += 1
            b2g[ballotid] = group_idx
            g2b.setdefault(group_idx, []).append(ballotid)
            group_infomap[group_idx] = ballotprops

        # 3.) Finally, grab a set of exemplar images from each group
        for groupid, ballotids in g2b.iteritems():
            for i, ballotid in enumerate(ballotids):
                if i >= self.NUM_EXMPLS:
                    break
                group_exmpls.setdefault(groupid, []).append(ballotid)

        # 4.) Also, export to proj.group_results.csv, for integration with
        # quarantine/post-processing panels.
        all_attrtypes = set()
        for attrmode, attrtype_dicts in attrprops.iteritems():
            for attrtype, attrprops in attrtype_dicts.iteritems():
                all_attrtypes.add(attrtype)
        fields = ('ballotid', 'groupid') + tuple(sorted(tuple(all_attrtypes))) + ('pid',)
        csvfile = open(self.proj.grouping_results, 'wb')
        dictwriter = csv.DictWriter(csvfile, fieldnames=fields)
        try:
            dictwriter.writeheader()
        except:
            util_gui._dictwriter_writeheader(csvfile, fields)
        rows = []
        for ballotid, ballotprops in ballot_attrvals.iteritems():
            row = {}
            for attrtype, attrval in ballotprops.iteritems():
                row[attrtype] = attrval
            row['ballotid'] = ballotid
            row['groupid'] = b2g[ballotid]
            rows.append(row)
        dictwriter.writerows(rows)
        csvfile.close()

        print "...{0} ballots have made it this far past grouping...".format(len(ballot_attrvals))

        pickle.dump(group_infomap, open(pathjoin(self.proj.projdir_path,
                                                 self.proj.group_infomap), 'wb'),
                    pickle.HIGHEST_PROTOCOL)

        if all_attrs_tabulationonly() and os.path.exists(pathjoin(self.proj.projdir_path,
                                                                  self.proj.ballot_to_group)):
            # Don't overwrite these prior grouping files.
            return
        else:
            pickle.dump(b2g, open(pathjoin(self.proj.projdir_path,
                                           self.proj.ballot_to_group), 'wb'),
                        pickle.HIGHEST_PROTOCOL)
            pickle.dump(g2b, open(pathjoin(self.proj.projdir_path,
                                           self.proj.group_to_ballots), 'wb'),
                        pickle.HIGHEST_PROTOCOL)
            pickle.dump(group_exmpls, open(pathjoin(self.proj.projdir_path,
                                                    self.proj.group_exmpls), 'wb'),
                        pickle.HIGHEST_PROTOCOL)
        
    def on_verify_done(self, verify_results, quarantined_results):
        """ 
        Input:
            dict VERIFY_RESULTS: maps {attrtype: {attrval: [imgpath_i, ...]}}
            dict QUARANTINED_RESULTS: {attrtype: [patchpath_i, ...]}
        """
        print "...Verify Done!..."
        if config.TIMER:
            config.TIMER.stop_task("VerifyGrouping_Verify_H")
        attrs = pickle.load(open(self.proj.ballot_attributesfile, 'rb'))
        if exists_imgattr(self.proj):
            # Convert the attrpatchpaths in VERIFY_RESULTS back into 
            # voted imgpaths, using imgpatch2imgpath
            imgpatch2imgpath = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                         self.proj.imgpatch2imgpath), 'rb'))
            verify_results = apply_patch2imgpath_fix(verify_results, attrs, imgpatch2imgpath)
        else:
            imgpatch2imgpath = {}

        if exists_digattr(self.proj):
            # Munge the single-digit groups in GROUP_RESULTS into the normal
            # digitattr groups.
            digpatch2imgpath = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                         self.proj.digpatch2imgpath), 'rb'))
            verify_results = apply_singledigit_fix(verify_results, attrs, digpatch2imgpath)
        else:
            digpatch2imgpath = {}
        self.verify_results = verify_results

        img2bal = pickle.load(open(self.proj.image_to_ballot, 'rb'))
        partitions_map = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                   self.proj.partitions_map), 'rb'))
        partitions_invmap = pickle.load(open(pathjoin(self.proj.projdir_path,
                                                      self.proj.partitions_invmap), 'rb'))
        qballots = set()

        attrs = pickle.load(open(self.proj.ballot_attributesfile, 'rb'))
        attrmap = {} # maps {str attrtype: dict attr}
        for attr in attrs:
            attrmap['_'.join(sorted(attr['attrs']))] = attr
        # If groupingmode was PER_PARTITION, then QUARANTINED_RESULTS
        # will only have information about one ballot from each partition

        # TODO: If an attribute type is for-tabulationonly, then it
        # doesn't make sense to real-quarantine the ballot, since
        # we can still do target-extraction on it. (Especially so if
        # grpmode is PER_PARTITION - imagine quarantining thousands of
        # ballots simply for a tabulationonly attr!). I should allow
        # the user to manually label the attribute value for quarantined
        # ballots for tabulationonly, PER_PARTITION attributes. But for
        # not-tabulationonly, PER_BALLOT attributes, I should do a
        # real-quarantine for all quarantined ballots.
        # For now, just aggressively quarantine.
        for attrtype, patchpaths in quarantined_results.iteritems():
            for patchpath in patchpaths:
                imgpath = imgpatch2imgpath.get(patchpath, None)
                if imgpath == None:
                    imgpath, idx = digpatch2imgpath.get(patchpath, (None, None))
                    if imgpath == None:
                        print "Hey, imgpath is None. patchpath:", patchpath
                        pdb.set_trace()
                if not attrmap[attrtype]['grp_per_partition']:
                    # groupmode is GRP_PER_BALLOT
                    ballotids = set([img2bal[imgpath]])
                else:
                    ballotids = set()
                    for ballotid in partitions_map[partitions_invmap[img2bal[imgpath]]]:
                        ballotids.add(ballotid)
                qballots = qballots.union(ballotids)
                    
        print "...Quarantined {0} ballots from grouping...".format(len(qballots))

        pickle.dump(list(qballots), open(pathjoin(self.proj.projdir_path,
                                                  self.proj.grouping_quarantined), 'wb'))

class VerifyBallotAttributesPanel(VerifyOrFlagOverlaysPanel):
    def set_classes(self):
        VerifyOrFlagOverlaysPanel.set_classes(self)
        self.overlaypanelCls = VerifyBallotAttributes
        self.footerCls = VerifyBallotAttributesFooter

class VerifyBallotAttributesFooter(VerifyOrFlagOverlaysFooter):
    def onButton_quarantine(self, evt):
        curgroup = self.GetParent().overlaypanel.get_current_group()
        self.GetParent().overlaypanel.do_quarantine()
        # Also remove ballots from CURGROUP from every attribute
        self.GetParent().GetParent().GetParent().apply_quarantine(curgroup.imgpaths)

class VerifyBallotAttributes(VerifyOrFlagOverlays):
    def __init__(self, parent, *args, **kwargs):
        VerifyOrFlagOverlays.__init__(self, parent, *args, **kwargs)
        
    def start(self, imgpath_groups, group_exemplars, rlist_map, 
              patch2imgpath, digpatch2imgpath,
              do_align=False, bbs_map=None, ondone=None, auto_ondone=False,
              stateP=None):
        """
        Input:
            dict IMGPATH_GROUPS: {grouptag: [imgpath_i, ...]}
            dict GROUP_EXEMPLARS: maps {grouptag: [exmpl_imgpath_i, ...]}
            dict RLIST_MAP: maps {str imgpath: (groupID_0, ...)}
            dict PATCH2IMGPATH: maps {str patchpath: str imgpath}
            dict DIGPATCH2IMGPATH: maps {str digpatchpath: (str imgpath, int idx)}
            dict BBS_MAP: maps {(grouptag, imgpath): (x1,y1,x2,y2)}
            fn ONDONE: Function that accepts one argument:
                dict {grouptag: [obj group_i, ...]}
            bool AUTO_ONDONE: If True, then when all groups are gone,
                this will immediately call the ondone function.
        """
        self.patch2imgpath = patch2imgpath
        self.digpatch2imgpath = digpatch2imgpath
        VerifyOrFlagOverlays.start(self, imgpath_groups,
                                   group_exemplars, rlist_map,
                                   do_align=do_align, bbs_map=bbs_map,
                                   ondone=ondone, auto_ondone=auto_ondone,
                                   stateP=stateP)

    def remove_element_with(self, imgpath):
        """ For each group (self.groups, self.finished_groups), remove
        all elements whose patchpath maps to IMGPATH. 
        """
        for group in (self.groups + sum(self.finished_groups.values(), [])):
            removeit = []
            for patchpath in group.imgpaths:
                imgpath_this = self.patch2imgpath.get(patchpath, None)
                if imgpath_this == None:
                    imgpath_this, idx = self.digpatch2imgpath.get(patchpath, (None, None))
                if imgpath_this == None:
                    print "Hey, imgpath_this was None. patchpath:", patchpath
                    pdb.set_trace()
                if imgpath_this == imgpath:
                    removeit.append(patchpath)
            removeit = set(removeit)
            group.imgpaths = [imP for imP in group.imgpaths if imP not in removeit]

class VerifyBallotOverlaysMultCats(VerifyOverlaysMultCats):
    def start(self, proj, imgpath_cats, cat_exemplars, patch2imgpath,
              digpatch2imgpath, do_align=False,
              bbs_map_cats=None, ondone=None, verifypanelClass=None):
        self.proj = proj
        self.patch2imgpath = patch2imgpath
        self.digpatch2imgpath = digpatch2imgpath
        # maps {cat_tag: [patchpath_i, ...]}
        self.quarantine_results_cat = {}
        VerifyOverlaysMultCats.start(self, imgpath_cats,
                                     cat_exemplars,
                                     do_align=do_align,
                                     bbs_map_cats=bbs_map_cats,
                                     ondone=ondone, 
                                     verifypanelClass=verifypanelClass)

    def onPageChange(self, evt):
        old = evt.GetOldSelection()
        new = evt.GetSelection()
        if new in self.started_pages:
            return
        curcat = self.page2cat[new]
        imgpath_groups = self.imgpath_cats[curcat]
        exemplar_groups = self.cat_exemplars[curcat]
        bbs_map = self.bbs_map_cats.get(curcat, None)
        verifyoverlays = self.nb.GetPage(new)
        stateP = pathjoin(self.proj.projdir_path,
                          '_state_verifyoverlays_{0}.p'.format(curcat))
        verifyoverlays.start(imgpath_groups, exemplar_groups, None, 
                             self.patch2imgpath, self.digpatch2imgpath,
                             bbs_map=bbs_map, do_align=self.do_align, 
                             stateP=stateP,
                             ondone=self.on_cat_done, auto_ondone=True)
        self.started_pages[new] = True

    def apply_quarantine(self, patchpaths):
        """ Across all ballot attributes, quarantine ballots from IMGPATHS. """
        curpage = self.nb.GetSelection()
        pages = range(self.nb.GetPageCount())
        for patchpath in patchpaths:
            imgpath = self.patch2imgpath.get(patchpath, None)
            if imgpath == None:
                imgpath, idx = self.digpatch2imgpath.get(patchpath, (None, None))
            if imgpath == None:
                print "Hey, imgpath is None. Why? Patchpath:", patchpath
                pdb.set_trace()
            # Remove all elements from each group from each verifypanel 
            # with IMGPATH as an element.
            for p in pages:
                verifypanel = self.nb.GetPage(p)
                verifypanel.overlaypanel.remove_element_with(imgpath)
                verifypanel.overlaypanel.update_listbox()

    def on_cat_done(self, verify_results, quarantine_results):
        """ Called when a category is finished overlay verification.
        Input:
            dict VERIFY_RESULTS: {grouptag: [patchpath_i, ...]}
            list QUARANTINE_RESULTS: [patchpath_i, ...]
        """
        print "...In on_cat_done..."
        curcat = self.page2cat[self.nb.GetSelection()]
        self.verify_results_cat[curcat] = verify_results
        self.quarantine_results_cat[curcat] = quarantine_results

        if len(self.verify_results_cat) == len(self.cat2page):
            print "We're done verifying all categories!"
            self.Disable()
            wx.MessageDialog(self, style=wx.OK,
                             message="You've finished verifying all \
categories.\n\n\
You may proceed to the next task.",
                             caption="Grouping Verification Completed").ShowModal()
            if self.ondone:
                self.ondone(self.verify_results_cat, self.quarantine_results_cat)
        else:
            wx.MessageDialog(self, style=wx.OK,
                             message="You've finished verifying category '{0}'.\n\n\
You may move onto the next category.".format(curcat),
                             caption="Category Completed").ShowModal()

def exists_imgattr(proj):
    attrs = pickle.load(open(proj.ballot_attributesfile, 'rb'))
    for attr in attrs:
        if not attr['is_digitbased']:
            return True
    return False
def exists_digattr(proj):
    attrs = pickle.load(open(proj.ballot_attributesfile, 'rb'))
    for attr in attrs:
        if attr['is_digitbased']:
            return True
    return False

def create_groups(proj):
    """
    Input:
        obj PROJ:
    Output:
        dict IMGPATH_GROUPS. IMGPATH_GROUPS maps
            {attrtype: {attrval: [imgpath_i, ...]}}
    """
    if not os.path.exists(pathjoin(proj.projdir_path, proj.extract_results)):
        return {}
    extract_results = pickle.load(open(pathjoin(proj.projdir_path,
                                                proj.extract_results), 'rb'))
    digitgroup_results = pickle.load(open(pathjoin(proj.projdir_path,
                                                   proj.digitgroup_results), 'rb'))
    b2imgs = pickle.load(open(proj.ballot_to_images, 'rb'))
    img2page = pickle.load(open(pathjoin(proj.projdir_path,
                                         proj.image_to_page), 'rb'))
    attrs = pickle.load(open(proj.ballot_attributesfile, 'rb'))
    imgpath_groups0 = create_imgbased_groups(extract_results, attrs,
                                             b2imgs, img2page, proj)
    imgpath_groups1 = create_digitbased_groups(digitgroup_results, 
                                               attrs, b2imgs, img2page, proj)
    return dict(imgpath_groups0.items() + imgpath_groups1.items())

def create_imgbased_groups(extract_results, attrs, b2imgs, img2page, proj):
    """
    Input:
        dict EXTRACT_RESULTS: maps {int ballotID: {attrtype: {'attrOrder': attrorder, 'err': err,
                                                              'exemplar_idx': exemplar_idx,
                                                              'patchpath': patchpath}}}
        dict MULTEXEMPLARS_MAP: maps {attrtype: {attrval: [(subpatchP, blankP, (x1,y1,x2,y2)), ...]}}
        list ATTRS: [dict attr_i, ...]
    Output:
        dict IMGPATH_GROUPS_CATS. IMGPATH_GROUPS_CATS maps
            {attrtype: {attrval: [imgpath_i, ...]}}.
    """
    if not extract_results:
        return {}
    multexemplars_map = pickle.load(open(pathjoin(proj.projdir_path,
                                                  proj.multexemplars_map), 'rb'))
    groups = {}
    # Prepopulate GROUPS with all possible attrtype->attrval combinations.
    for attrtype, stuffdict in multexemplars_map.iteritems():
        for attrval in stuffdict:
            groups.setdefault(attrtype, {})[attrval] = []
    for ballotid, attrtypedicts in extract_results.iteritems():
        for attrtype, attrdict in attrtypedicts.iteritems():
            attrOrder = attrdict['attrOrder']
            patchpath = attrdict['patchpath']
            attrval = attrOrder[0]
            groups.setdefault(attrtype, {}).setdefault(attrval, []).append(patchpath)
    return groups

def create_digitbased_groups(digitgroup_results, attrs, b2imgs, img2page, proj):
    """
    Input:
        dict DIGITGROUP_RESULTS: maps {str digattrtype: {int ID: [str digitstr, imgpath, [str digit_i,(x1,y1,x2,y2),score_i,digpatchpath],...]}}.
            If GROUP_MODE is by partition, then ID is partitionID. If GROUP_MODE
            is by ballot, then ID is ballotID.
        dict DIGMULTEXEMPLARS_MAP: maps {str digit: [(regionP, (x1,y1,x2,y2), exmplrP), ...]}
        list ATTRS: [dict attr_i, ...]
    Output:
        dict IMGPATH_GROUPS. IMGPATH_GROUPS maps
            {attrtype: {attrval: [imgpath_i, ...]}}.
            particular, this splits up by digit.
    """
    def get_side(attrs, attrtype):
        for attr in attrs:
            attrtypestr = '_'.join(sorted(attr['attrs']))
            if attrtypestr == attrtype:
                return attr['side']
        print "Badness -- couldn't find attribute {0}.".format(attrtype)
        pdb.set_trace()
        return None
    if not digitgroup_results:
        return {}
    digmultexemplars_map = pickle.load(open(pathjoin(proj.projdir_path,
                                                     proj.digitmultexemplars_map), 'rb'))
    imgpath_groups = {} # maps {(attrtype,digit): [imgpath_i, ...]}
    for attrtype, info in digitgroup_results.iteritems():
        # Prepopulate IMGPATH_GROUPS with every attrtype->digit combination
        for digitval in digmultexemplars_map:
            imgpath_groups.setdefault(attrtype, {})[digitval] = []
        page = get_side(attrs, attrtype)
        for ID, digitmats in info.iteritems():
            digitstr, imgpath, digitinfo = digitmats
            for idx, (digit, (x1,y1,x2,y2), score, digpatchpath) in enumerate(digitinfo):
                imgpath_groups.setdefault(attrtype, {}).setdefault(digit, []).append(digpatchpath)
    return imgpath_groups

def get_group_exemplars(proj):
    """ For each grouplabel L, return an exemplar imgpath that visually
    represents L.
    Input:
        obj PROJ:
    Output:
        dict GROUP_EXEMPLARS. maps {attrtype: {attrval: [imgpath_i, ...]}}
    """
    digit_exemplars = get_digit_exemplars(proj)
    img_exemplars = get_img_exemplars(proj)
    return dict(digit_exemplars.items() + img_exemplars.items())

def get_img_exemplars(proj):
    # MULTEXEMPLARS_MAP: maps {attrtype: {attrval: [(subpatchP, blankpath, (x1,y1,x2,y2)), ...]}}
    if not exists_imgattr(proj):
        return {}
    multexemplars_map = pickle.load(open(pathjoin(proj.projdir_path,
                                                  proj.multexemplars_map), 'rb'))
    exemplars = {} 
    for attrtype, attrdict in multexemplars_map.iteritems():
        for attrval, tuples in attrdict.iteritems():
            for (subpatchP, blankpath, (x1,y1,x2,y2)) in tuples:
                exemplars.setdefault(attrtype, {}).setdefault(attrval, []).append(subpatchP)
    return exemplars

def get_digit_exemplars(proj):
    if not exists_digattr(proj):
        return {}
    attrs = pickle.load(open(proj.ballot_attributesfile, 'rb'))
    digattrtype = None
    for attr in attrs:
        if attr['is_digitbased']:
            digattrtype = '_'.join(sorted(attr['attrs']))
            break
    if digattrtype == None:
        # Means there are no digit attributes in this election
        return {}
    elif is_part_consistent(proj, digattrtype):
        # Means digit-based grouping was not run, as it is per-partition consistent
        return {}
    # dict DIGIT_EXEMPLARS: maps {str digit: [(regionpath_i, (x1,y1,x2,y2), exemplarpath_i), ...]}
    digit_exemplars = pickle.load(open(pathjoin(proj.projdir_path, proj.digitmultexemplars_map), 'rb'))
    group_exemplars = {}
    for digit, exemplars_info in digit_exemplars.iteritems():
        exemplar_imgpaths = []
        for (regionpath, (x1,y1,x2,y2), exemplarpath) in exemplars_info:
            exemplar_imgpaths.append(exemplarpath)
        group_exemplars.setdefault(digattrtype, {})[digit] = exemplar_imgpaths
    return group_exemplars

def is_part_consistent(proj, attrtype):
    attrs = pickle.load(open(proj.ballot_attributesfile, 'rb'))
    for attr in attrs:
        attrtype_str = '_'.join(sorted(attr['attrs']))
        if attrtype_str == attrtype:
            return attr['grp_per_partition']
    raise Exception("Attribute '{0}' doesn't exist in ballot_attributesfile?!".format(attrtype))

def get_rlist_map(proj):
    """
    Input:
        obj PROJ:
    Output:
        dict RLIST_MAP. maps {str imgpath: (groupID_0, ...)}
    """
    return {}

def apply_patch2imgpath_fix(verify_results, attrs, imgpatch2imgpath):
    """ Converts patchpaths to ballotids, for img-based attributes.  """
    def is_imgbased(attrs, attrtype):
        for attr in attrs:
            attrtypestr = '_'.join(sorted(attr['attrs']))
            if attrtypestr == attrtype:
                return not attr['is_digitbased']
        print "Uh oh, couldn't find attrtype {0}.".format(attrtype)
        pdb.set_trace()
    out = {}
    for attrtype, attrvaldict in verify_results.iteritems():
        for attrval, patchpaths in attrvaldict.iteritems():
            if not is_imgbased(attrs, attrtype):
                out.setdefault(attrtype, {})[attrval] = patchpaths
            else:
                imgpaths = [imgpatch2imgpath[patchpath] for patchpath in patchpaths]
                out.setdefault(attrtype, {})[attrval] = imgpaths
    return out

def apply_singledigit_fix(verify_results, attrs, digpatch2imgpath):
    """ Converts the individual digit 'attributes' back into the original
    digit-based attribute.
    Input:
        dict VERIFY_RESULTS: maps {attrtype: {attrval: [imgpath_i, ...]}}
        list ATTRS: list of attr dicts, [dict attr_i, ...]
        dict DIGPATCH2IMGPATH: maps {digpatchpatch: (str imgpath, int idx)}
    Output:
        dict VERIFY_RESULTS_FIX: maps {attrtype: {attrval: [imgpath_i, ...]}}
    """
    digitattrtype = None
    for attr in attrs:
        if attr['is_digitbased']:
            digitattrtype = '_'.join(sorted(attr['attrs']))
            break
    assert digitattrtype != None
    
    d_map = {} # maps {imgpath: {int idx: str digit}}
    verify_results_fixed = {}

    for attrtype, attrvaldict in verify_results.iteritems():
        for attrval, digpatchpaths in attrvaldict.iteritems():
            if attrtype == digitattrtype:
                for digpatchpath in digpatchpaths:
                    imgpath, idx = digpatch2imgpath[digpatchpath]
                    d_map.setdefault(imgpath, {})[idx] = attrval
            else:
                verify_results_fixed.setdefault(attrtype, {})[attrval] = digpatchpaths
            
    for imgpath, digitidx_map in d_map.iteritems():
        digits_lst = []
        for i, idx in enumerate(sorted(digitidx_map.keys())):
            if i != idx:
                pdb.set_trace()
            assert i == idx
            digits_lst.append(digitidx_map[idx])
        digitstrval = ''.join(digits_lst)
        print "For imgP {0}, digitval is: {1}".format(imgpath, digitstrval)
        verify_results_fixed.setdefault(digitattrtype, {}).setdefault(digitstrval, []).append(imgpath)
    return verify_results_fixed

def read_sscustattr(sspath):
    """ Reads in the SSPATH csv file, and returns it as a dictionary for
    more efficient retrievals.
    """
    reader = csv.DictReader(open(sspath, 'rb'))
    outdict = {} # maps {str in: str out}
    for row in reader:
        outdict[row['in']] = row['out']
    return outdict
