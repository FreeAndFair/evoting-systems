import os, sys, csv, datetime, argparse
try:
    import cPickle as pickle
except ImportError as e:
    import pickle

from os.path import join as pathjoin

import wx

sys.path.append('..')
from projconfig_new.project_panel import ProjectPanel, Project
from projconfig_new.config_panel import ConfigPanel
from partitions.partition_panel import PartitionMainPanel
from specify_voting_targets.select_targets import SelectTargetsMainPanel
from labelcontest.labelcontest import LabelContest
from grouping.ballot_attributes import BallotAttributesPanel, ATTRMODE_CUSTOM
from digits_ui.labeldigits import LabelDigitsPanel
from grouping.run_grouping import RunGroupingMainPanel
from grouping.verify_grouping_panel import VerifyGroupingMainPanel
from runtargets.extract_targets_new import TargetExtractPanel
from threshold.threshold import ThresholdPanel
from quarantine.quarantinepanel import QuarantinePanel
from post_processing.postprocess import ResultsPanel

import specify_voting_targets.util_gui as util_gui
import config, util

"""
The main module for OpenCount.
"""

PROJROOTDIR = 'projects_new'

class MainFrame(wx.Frame):
    PROJECT = 0
    CONFIG = 1
    PARTITION = 2
    BALLOT_ATTRIBUTES = 3
    LABEL_DIGATTRS = 4
    RUN_GROUPING = 5
    CORRECT_GROUPING = 6
    SELTARGETS = 7
    LABEL_CONTESTS = 8
    TARGET_EXTRACT = 9
    SET_THRESHOLD = 10
    QUARANTINE = 11
    PROCESS = 12

    def __init__(self, parent, *args, **kwargs):
        wx.Frame.__init__(self, parent, title="OpenCount", *args, **kwargs)

        # PROJECT: Current Project being worked on.
        self.project = None

        self.init_ui()

        self.Bind(wx.EVT_NOTEBOOK_PAGE_CHANGED, self.onPageChange)
        self.Bind(wx.EVT_NOTEBOOK_PAGE_CHANGING, self.onPageChanging)
        self.Bind(wx.EVT_CLOSE, self.onClose)

        self.notebook.ChangeSelection(0)
        self.notebook.SendPageChangedEvent(-1, 0)

    def init_ui(self):
        self.notebook = wx.Notebook(self)
        self.setup_pages()
        self.Maximize()

    def setup_pages(self):
        self.panel_projects = ProjectPanel(self.notebook)
        self.panel_config = ConfigPanel(self.notebook)
        self.panel_partition = PartitionMainPanel(self.notebook)
        self.panel_ballot_attributes = BallotAttributesPanel(self.notebook)
        self.panel_label_digitattrs = LabelDigitsPanel(self.notebook)
        self.panel_run_grouping = RunGroupingMainPanel(self.notebook)
        self.panel_correct_grouping = VerifyGroupingMainPanel(self.notebook)
        self.panel_seltargets = SelectTargetsMainPanel(self.notebook)
        self.panel_label_contests = LabelContest(self.notebook, self.GetSize())
        self.panel_target_extract = TargetExtractPanel(self.notebook)
        self.panel_set_threshold = ThresholdPanel(self.notebook, self.GetSize())
        self.panel_quarantine = QuarantinePanel(self.notebook)
        self.panel_process = ResultsPanel(self.notebook)
        self.pages = [(self.panel_projects, "Projects", "Projects"),
                      (self.panel_config, "Import Files", "Import"),
                      (self.panel_partition, "Partition Ballots", "Partition"),
                      (self.panel_ballot_attributes, "Ballot Attributes", "Attrs"),
                      (self.panel_label_digitattrs, "Label Digit-Based Attributes", "Label Digit Attrs"),
                      (self.panel_run_grouping, "Run Grouping", "Group"),
                      (self.panel_correct_grouping, "Correct Grouping", "Correct Grouping"),
                      (self.panel_seltargets, "Select Voting Targets", "Targets"),
                      (self.panel_label_contests, "Label Contests", "Contests"),
                      (self.panel_target_extract, "Extract Targets", "Extract"),
                      (self.panel_set_threshold, "Set Threshold", "Threshold"),
                      (self.panel_quarantine, "Process Quarantine", "Quarantine"),
                      (self.panel_process, "Results", "Results")]
        self.titles = {}
        for panel, fullname, shortname in self.pages:
            self.notebook.AddPage(panel, shortname)
            self.titles[panel] = (fullname, shortname)
    def onPageChanging(self, evt):
        old = evt.GetOldSelection()
        new = evt.GetSelection()
        if old == -1:
            # Don't know why these events are sometimes triggered...
            return

        if old == MainFrame.PROJECT:
            status, msg = self.panel_projects.can_move_on()
            if status:
                self.project = self.panel_projects.get_project()
                self.SetTitle("OpenCount -- Project {0}".format(self.project.name))
            else:
                dlg = wx.MessageDialog(self, message=msg, style=wx.ID_OK)
                dlg.ShowModal()
                evt.Veto()
            return

        curpanel = self.notebook.GetPage(old)
        if hasattr(curpanel, 'can_move_on'):
            if not curpanel.can_move_on():
                wx.MessageDialog(self, message="Error: You can not \
proceed. Please address the prior warnings first.",
                                 caption="OpenCount: Can't go on",
                                 style=wx.OK).ShowModal()
                evt.Veto()
                return
        else:
            print "(Warning) Class {0} has no can_move_on method.".format(curpanel)

        if old == MainFrame.CONFIG:
            self.panel_config.stop()
        elif old == MainFrame.PARTITION:
            self.panel_partition.stop()
            if config.TIMER:
                config.TIMER.stop_task("Partition_Total")
        elif old == MainFrame.BALLOT_ATTRIBUTES:
            self.panel_ballot_attributes.stop()
            if config.TIMER:
                config.TIMER.stop_task("BallotAttributes_Total")
        elif old == MainFrame.LABEL_DIGATTRS:
            self.panel_label_digitattrs.stop()
            if config.TIMER:
                config.TIMER.stop_task("LabelDigitAttrs_Total")
        elif old == MainFrame.RUN_GROUPING:
            self.panel_run_grouping.stop()
            if config.TIMER:
                config.TIMER.stop_task("RunGrouping_Total")
        elif old == MainFrame.CORRECT_GROUPING:
            self.panel_correct_grouping.stop()
            if config.TIMER:
                config.TIMER.stop_task("CorrectGrouping_Total")
        elif old == MainFrame.SELTARGETS:
            self.panel_seltargets.stop()
            if config.TIMER:
                config.TIMER.stop_task("SelectTargets_Total")
        elif old == MainFrame.LABEL_CONTESTS:
            self.panel_label_contests.stop()
            if config.TIMER:
                config.TIMER.stop_task("LabelContests_Total")
        elif old == MainFrame.TARGET_EXTRACT:
            self.panel_target_extract.stop()
            if config.TIMER:
                config.TIMER.stop_task("TargetExtract_Total")
        elif old == MainFrame.SET_THRESHOLD:
            self.panel_set_threshold.stop()
            if config.TIMER:
                config.TIMER.stop_task("SetThreshold_Total")
        elif old == MainFrame.QUARANTINE:
            self.panel_quarantine.stop()
            if config.TIMER:
                config.TIMER.stop_task("Quarantine_Total")
        elif old == MainFrame.PROCESS:
            pass

    def onPageChange(self, evt):
        old = evt.GetOldSelection()
        new = evt.GetSelection()

        if self.project:
            self.project.save()
        if config.TIMER:
            config.TIMER.dump()

        if old != -1:
            curpanel = self.notebook.GetPage(old)
            self.notebook.SetPageText(old, self.titles[curpanel][1])
        newpanel = self.notebook.GetPage(new)
        self.notebook.SetPageText(new, self.titles[newpanel][0])

        if new >= MainFrame.SELTARGETS:
            if not os.path.exists(pathjoin(self.project.projdir_path,
                                           self.project.group_to_ballots)):
                # Grouping wasn't performed, which means that we should
                # simply use the partitions as the groups, since the user
                # 'knows' that the partitions also specify a grouping.
                if not os.path.exists(pathjoin(self.project.projdir_path,
                                               self.project.partitions_map)):
                    print "(Notice) Couldn't find {0}. Was decoding not performed?".format(pathjoin(self.project.projdir_path,
                                                                                                    self.project.partitions_map))
                    dlg = wx.MessageDialog(self, style=wx.OK,
                                           message="You must first run Decoding (Partitioning) \
before proceeding to this step. OpenCount will take you there now.")
                    dlg.ShowModal()
                    self.notebook.ChangeSelection(self.PARTITION)
                    self.notebook.SendPageChangedEvent(self.SELTARGETS, self.PARTITION)
                    return
                    
                print "(Notice) No Attributes Exists, so, using Partitioning as the Grouping."
                partitions_map = pickle.load(open(pathjoin(self.project.projdir_path,
                                                           self.project.partitions_map), 'rb'))
                partitions_invmap = pickle.load(open(pathjoin(self.project.projdir_path,
                                                              self.project.partitions_invmap), 'rb'))
                partition_exmpls = pickle.load(open(pathjoin(self.project.projdir_path,
                                                             self.project.partition_exmpls), 'rb'))

                # The GRP_INFOMAP should just contain partitionid info.
                grp_infomap = {} # maps {int groupID: {str prop: str val}}
                grp2bals = {}
                bal2grp = {}
                grpexmpls = {}
                curgroupid = 0
                for (partitionid, ballotids) in sorted(partitions_map.iteritems()):
                    if not ballotids:
                        continue
                    propdict = {'pid': partitionid}
                    grp_infomap[curgroupid] = propdict
                    #print 'extend', curgroupid, 'by', ballotids
                    grp2bals.setdefault(curgroupid, []).extend(ballotids)
                    for ballotid in ballotids:
                        bal2grp[ballotid] = curgroupid
                    curgroupid += 1
                curgroupid = 0
                for (partitionid, ballotids) in sorted(partition_exmpls.iteritems()):
                    if not ballotids:
                        continue
                    grpexmpls[curgroupid] = ballotids
                    curgroupid += 1

                # Also, export to proj.group_results.csv, for integration with
                # quarantine/post-processing panels.
                #print "SET TO", grp2bals
                fields = ('ballotid', 'groupid')
                csvfile = open(self.project.grouping_results, 'wb')
                dictwriter = csv.DictWriter(csvfile, fieldnames=fields)
                try:
                    dictwriter.writeheader()
                except:
                    util_gui._dictwriter_writeheader(csvfile, fields)
                rows = []
                for ballotid, groupid in bal2grp.iteritems():
                    rows.append({'ballotid': ballotid, 'groupid': groupid})
                dictwriter.writerows(rows)
                csvfile.close()

                pickle.dump(grp2bals, open(pathjoin(self.project.projdir_path,
                                                    self.project.group_to_ballots), 'wb'),
                            pickle.HIGHEST_PROTOCOL)
                pickle.dump(bal2grp, open(pathjoin(self.project.projdir_path,
                                                   self.project.ballot_to_group), 'wb'),
                            pickle.HIGHEST_PROTOCOL)
                pickle.dump(grpexmpls, open(pathjoin(self.project.projdir_path,
                                                     self.project.group_exmpls), 'wb'),
                            pickle.HIGHEST_PROTOCOL)
                pickle.dump(grp_infomap, open(pathjoin(self.project.projdir_path,
                                                       self.project.group_infomap), 'wb'),
                            pickle.HIGHEST_PROTOCOL)

        if new == MainFrame.PROJECT:
            self.panel_projects.start(PROJROOTDIR)
        elif new == MainFrame.CONFIG:
            self.panel_config.start(self.project, pathjoin(self.project.projdir_path,
                                                           '_state_config.p'))
        elif new == MainFrame.PARTITION:
            if config.TIMER:
                config.TIMER.start_task("TOTALTIME")
            if config.TIMER:
                config.TIMER.start_task("Partition_Total")
            self.panel_partition.start(self.project, pathjoin(self.project.projdir_path,
                                                              '_state_partition.p'))
        elif new == MainFrame.BALLOT_ATTRIBUTES:
            # A (crude) way of detecting if the user started working on
            # ballot attributes already
            is_attrs_started = os.path.exists(pathjoin(self.project.projdir_path,
                                                       '_state_ballot_attributes.p'))
            if not is_attrs_started:
                dlg = wx.MessageDialog(self, style=wx.YES_NO,
                                       message="Do you wish to define any Ballot \
Attributes? \n\n\
If you intend to define ballot attributes (precinct number, tally group, etc.), then \
click 'Yes'.\n\n\
Otherwise, click 'No'.")
                resp = dlg.ShowModal()
                if resp == wx.ID_NO:
                    dlg = wx.MessageDialog(self, style=wx.OK,
                                           message="You indicated that you \
do not want to define any Ballot Attributes.\n\n\
You will now be taken to the Ballot Annotation stage.")
                    dlg.ShowModal()
                    self.notebook.ChangeSelection(self.SELTARGETS)
                    self.notebook.SendPageChangedEvent(self.BALLOT_ATTRIBUTES, self.SELTARGETS)
                    return
                
            if config.TIMER:
                config.TIMER.start_task("BallotAttributes_Total")
            self.panel_ballot_attributes.start(self.project, pathjoin(self.project.projdir_path,
                                                                      '_state_ballot_attributes.p'))
        elif new == MainFrame.LABEL_DIGATTRS:
            if config.TIMER:
                config.TIMER.start_task("LabelDigitAttrs_Total")
            # Skip if there are no digit-based attributes
            if not exists_digitbasedattr(self.project):
                dlg = wx.MessageDialog(self, message="There are no Digit-Based \
Attributes in this election -- skipping to the next page.", style=wx.OK)
                dlg.ShowModal()
                self.notebook.ChangeSelection(self.RUN_GROUPING)
                self.notebook.SendPageChangedEvent(self.LABEL_DIGATTRS, self.RUN_GROUPING)
            else:
                self.panel_label_digitattrs.start(self.project)
        elif new == MainFrame.RUN_GROUPING:
            if config.TIMER:
                config.TIMER.start_task("RunGrouping_Total")
            if not exists_imgattr(self.project) and not exists_digitbasedattr(self.project):
                dlg = wx.MessageDialog(self, message="There are no attributes \
to group in this election -- skipping to the next page.", style=wx.OK)
                dlg.ShowModal()
                dst_page = self.SELTARGETS if not exists_custattr(self.project) else self.CORRECT_GROUPING
                self.notebook.ChangeSelection(dst_page)
                self.notebook.SendPageChangedEvent(self.RUN_GROUPING, dst_page)
            else:
                self.panel_run_grouping.start(self.project, pathjoin(self.project.projdir_path,
                                                                     '_state_run_grouping.p'))
        elif new == MainFrame.CORRECT_GROUPING:
            if config.TIMER:
                config.TIMER.start_task("CorrectGrouping_Total")
            if not exists_imgattr(self.project) and not exists_digitbasedattr(self.project) and not exists_custattr(self.project):
                dlg = wx.MessageDialog(self, message="There are no attributes \
to verify grouping for in this election -- skipping to the next page.", style=wx.OK)
                dlg.ShowModal()
                self.notebook.ChangeSelection(self.SELTARGETS)
                self.notebook.SendPageChangedEvent(self.CORRECT_GROUPING, self.SELTARGETS)
            else:
                self.panel_correct_grouping.start(self.project, pathjoin(self.project.projdir_path,
                                                                         '_state_correct_grouping.p'))
        elif new == MainFrame.SELTARGETS:
            if config.TIMER:
                config.TIMER.start_task("SelectTargets_Total")
            self.panel_seltargets.start(self.project, pathjoin(self.project.projdir_path,
                                                               '_state_selecttargetsMain.p'),
                                        self.project.ocr_tmp_dir)
        elif new == MainFrame.LABEL_CONTESTS:
            """ Requires:
                proj.target_locs_dir -- Location of targets
                proj.patch_loc_dir -- For language, and *something* else.
            """
            if config.TIMER:
                config.TIMER.start_task("LabelContests_Total")
            self.panel_label_contests.proj = self.project
            img2flip = pickle.load(open(pathjoin(self.project.projdir_path,
                                                 self.project.image_to_flip), 'rb'))
            sz = self.GetSize()
            self.panel_label_contests.start(sz)
            self.SendSizeEvent()
        elif new == MainFrame.TARGET_EXTRACT:
            if config.TIMER:
                config.TIMER.start_task("TargetExtract_Total")
            self.panel_target_extract.start(self.project)
        elif new == MainFrame.SET_THRESHOLD:
            if config.TIMER:
                config.TIMER.start_task("SetThreshold_Total")
            sz = self.GetSize()
            self.panel_set_threshold.start(self.project, size=sz)
            self.SendSizeEvent()
        elif new == MainFrame.QUARANTINE:
            if config.TIMER:
                config.TIMER.start_task("Quarantine_Total")
            self.panel_quarantine.start(self.project, self.GetSize())
        elif new == MainFrame.PROCESS:
            if config.TIMER:
                config.TIMER.start_task("GenerateResults_Total")
            self.panel_process.start(self.project)
            if config.TIMER:
                config.TIMER.stop_task("GenerateResults_Total")
                config.TIMER.stop_task("TOTALTIME")
                config.TIMER.dump()

    def onClose(self, evt):
        """
        Triggered when the user/program exits/closes the MainFrame.
        """
        if self.project:
            self.project.save()
        if config.TIMER:
            config.TIMER.stop_task("TOTALTIME")
            config.TIMER.dump()
        for fn in Project.closehook:
            fn()
        evt.Skip()

def exists_digitbasedattr(proj):
    if not exists_attrs(proj):
        return False
    attrs = pickle.load(open(proj.ballot_attributesfile, 'rb'))
    for attr in attrs:
        if attr['is_digitbased']:
            return True
    return False
def exists_imgattr(proj):
    if not exists_attrs(proj):
        return False
    attrs = pickle.load(open(proj.ballot_attributesfile, 'rb'))
    for attr in attrs:
        if not attr['is_digitbased']:
            return True
    return False
def exists_custattr(proj):
    if not exists_attrs(proj):
        return False
    attrprops = pickle.load(open(pathjoin(proj.projdir_path, proj.attrprops), 'rb'))
    return len(attrprops[ATTRMODE_CUSTOM]) != 0

def exists_attrs(proj):
    """ Doesn't account for custom attrs. """
    if not os.path.exists(proj.ballot_attributesfile):
        return False
    ballot_attributesfile = pickle.load(open(proj.ballot_attributesfile, 'rb'))
    if not ballot_attributesfile:
        return False
    else:
        return True

def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("-n", "--num", type=int, dest='n',
                        help="Only process the first N ballots.")
    parser.add_argument("--time", metavar="PREFIX",
                        help="OpenCount will output timing statistics \
to a logfile. If PREFIX is given as 'foo', then the output filename \
is: \n\
        foo_YEAR_MONTH_DAY_HOUR_MINUTE.log")
    parser.add_argument("--dev", action='store_true',
                        help="Run OpenCount in Development mode. This \
enables a few dev-specific buttons in the UI which are useful when \
debugging projects.")
    return parser.parse_args()

def main():
    args = parse_args()
    if args.n:
        print "(Info) Processing first {0} ballots [user passed in -n,--num]".format(args.n)
        config.BALLOT_LIMIT = args.n
    config.IS_DEV = args.dev
    if config.IS_DEV:
        print "(Info) Running in dev-mode"
    if args.time:
        prefix = args.time
        now = datetime.datetime.now()
        date_suffix = "{0}_{1}_{2}_{3}_{4}".format(now.year, now.month, now.day,
                                                   now.hour, now.minute)
        # "PREFIX_YEAR_MONTH_DAY_HOUR_MINUTE.log"
        timing_filepath = "{0}_{1}.log".format(prefix, date_suffix)
        config.TIMER = util.MyTimer(timing_filepath)
        print "(Info) User passed in '--time': Saving timing statistics to {0}".format(timing_filepath)

    app = wx.App(False)
    f = MainFrame(None, size=wx.GetDisplaySize())
    f.Show()
    app.MainLoop()

if __name__ == '__main__':
    main()
