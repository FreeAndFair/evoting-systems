from maingui import MainFrame
import csv

def run_all(proj):
    for i in [MainFrame.PROJECTS, MainFrame.CONFIG, 
              MainFrame.SELECT_TARGETS, MainFrame.LABEL_CONTESTS, 
              MainFrame.DEFINE_ATTRIBUTES, MainFrame.LABEL_ATTRS, 
              MainFrame.CORRECT_GROUPING, MainFrame.RUN, 
              MainFrame.SET_THRESHOLD, MainFrame.QUARANTINE, 
              MainFrame.PROCESS]:
        run(proj, i)

def run(proj, tab):
    """
    Verify that everything is okay up until this point.
    If something is not, it means that things will break further along
      and we should stop now and give an error message.
    Otherwise we will reach post processing and try to tally everything
      together, and will get some crash which will take forever to debug.
      
    Each method returns either true or false
      True indicates all is well.
      False indicates something is wrong and will break future pieces.
    """
    is_okay, reason = run_single(proj, tab)
    if not is_okay:
        raise Exception(reason)

def run_single(proj, tab):
    if tab == MainFrame.LABEL_CONTESTS:
        return check_label_contests(proj)
        
    return True, "OK"


def check_label_contests(proj):
    def text_consistent():
        """
        Check that the text it's outputted is consistent.
        """
        contest_text = {}
        for line in csv.reader(open(proj.contest_text)):
            contest_text[line[0]] = line[1:]
        for line in csv.reader(open(proj.contest_id)):
            if len(contest_text[line[2]])+1 != len(line):
                return False, "In ballot " + line[0] +  ", contest with GID " + contest_text[line[2]] + " has order of order [" + (", ".join(line[3:])) + "]" + " but has targets " + (", ".join(contest_text[line[3]])) + "."
        return True, "OK"

    for fn in [text_consistent]:
        ok, err = fn()
        if not ok:
            return ok, err
    return True, "OK"
            
