#!/usr/bin/env python
import config
import const 
import pdb
import db
import os
import subprocess
import sys
import util

global log
"""
summarize_results.py

Do basic summaries whether from database or from results files.

When operating from results files, we try merging similar contest
and choice names, locating them in function "is_this_like_them"; 
the merge entries are placed into merge dictionaries in 
enter_merge_src_and_dest, and all incoming text is translated
through the dictionaries created by this function.

The basic merge capability looks for variants where almost
all the letters are identical or in similarly shaped letter groups,
and also merges on one one-character slip, e.g.: Wce Pres --> Vice Pres 

For most contests, 30 chars should uniquely identify them,
so we take only the first 30 chars from the database
to provide some grouping. Similarly, we take only 15 chars from
the database for choices.

TBD:
We should be able to make inferences about variant choices
by grouping all variant choices for a given contest and
checking for highly similar variants.

We should be able to make inferences about variant contests
by getting all the choices for each variant contest and seeing
how similar the various sets of choices are.

When variants are located which only appear in a small subset
of layoutcodes, they are good candidates for merging with similar
variants which appear in a larger subset of layout codes, so 
we must weight variants by how many layout codes they appear within.

Whether our output is from the database or from the results files,
we generate summary csv files and invoke ooffice (Open Office) to
import the csv material for viewing and printing.

"""

queries = [
    ("""select count(*), substring(contest_text,1,30) as contest, 
       substring(choice_text,1,15) as choice
       from voteops where was_voted 
       group by contest, choice
       order by contest, choice""",
     "summary.csv",
     "election wide summary"),
    ("""select count(code_string), 
code_string, 
substring(contest_text,1,30) as contest, 
substring(choice_text,1,15) as choice
from voteops join ballots on voteops.ballot_id = ballots.ballot_id
where was_voted
group by code_string, contest_text, choice_text
order by code_string""",
    "bylayout.csv",
    "precinct summaries (identified by layout code)"
)
]

# dictionaries holding only the contest and choice names
contest_name_dict = {}
choice_name_dict = {}

# voted_dict is keyed off (contest name, choice name) and holds vote count 
# layout_voted_dict is keyed off (layout, contest name, choice name) 
# and holds vote counts per layout
layout_voteop_dict = {}
voteop_dict = {}
voted_dict = {}
layout_voted_dict = {}

# votecount_counts_dict is useful for overvote counts;
# it holds the number of times each contest was voted for once per ballot,
# twice per ballot, etc...
votecount_counts_dict = {}

# the merge dictionaries are keyed off of variants that are to be merged
# and hold the value to which the variant should be merged
contest_merge_dict = {}
choice_merge_dict = {}

def enter_merge_src_and_dest(a,blist,merge_dict):
    """ Eventually, solicit user opinion"""
    global log
    if len(blist)<1:
        log.debug("Cannot merge: empty choice list for '%s'" % (a,))
    merge_dict[a] = blist[0]
    log.info("Merge src: %s\nMerge dst: %s" % (a[:60],merge_dict[a][:60]))

def is_this_like_them(this,them):
    """If string 'this' is like any keys of dict 'them', return close matches"""
    min_chars = 5
    max_chars = 50
    max_misses = 4
    max_loc = 40

    central = lambda s: s.replace("dquot","").replace("squot","").replace(" ","").replace("comma","")[1:-1]

    olist = ("o","0","O","Q","C","a","e")
    rlist = ("r","n")
    llist = ("l","i","1","I","J","f","t")
    vlist = ("v","y")

    retlist = []

    # don't merge text with PROP or MEAS, 
    # since they may differ by only one letter
    if this.find("PROP")>=0 or this.find("MEAS")>=0:
        return retlist
    # don't merge text with numbers, since they may refer to 
    # different propositions, measures, districts, etc...
    for number in "0123456789":
        if this.find(number)>=0:
            return retlist
    # don't merge small strings; they may create false matches
    if len(this) < min_chars:
        return retlist

    cthis = central(this)
    for k in them:
        # match only on 5 or more characters
        if len(k) < min_chars:
            continue
        cthat = central(k)

        # match if central part of this is exact match in central part of that
        if ( len(cthis) > min_chars 
             and len(cthat) > min_chars 
             and cthat.find(cthis)>0 ):
            retlist.append(k)

        # match if all but one character in the first 50
        # are identical or easily swapped
        miss_count = 0
        miss_location = 0
        location = 0
        for c1,c2 in zip(cthis[:max_chars],cthat[:max_chars]):
            ok = True
            if c1<>c2:
                ok = False
                if c1 in rlist and c2 in rlist:
                    ok = True
                elif c1 in olist and c2 in olist:
                    ok = True
                elif c1 in llist and c2 in llist:
                    ok = True
                elif c1 in vlist and c2 in vlist:
                    ok = True
            if not ok:
                    miss_count += 1
                    miss_location = location
                    if miss_count >= max_misses:
                        break
            location += 1
        # if you have a substantial miss before the 40th character,
        # see if you can realign after the miss
        # by finding a match through the 49th character 
        # on a string of more than 5 characters length
        # starting within 1 of the miss
        realign = False
        if miss_count >= max_misses:
            if miss_location < max_loc:
                ml = miss_location
                that_in_this = cthis[ml:max_chars-1].find(cthat[ml:max_chars-1])
                this_in_that = cthat[ml:max_chars-1].find(cthis[ml:max_chars-1])
                if (
                    (len(cthat[ml:max_chars-1]) > min_chars)
                    and (len(cthis[ml:max_chars-1]) > min_chars)
                    and (
                        (that_in_this >= 0 and that_in_this <= 1)
                        or (this_in_that >= 0 and this_in_that <= 1)
                        )       
                    ):
                    realign = True
        if realign:
            retlist.append(k)
        elif ( (miss_count < max_misses 
                and len(cthis) > ((2*max_chars)/3) 
                and len(cthat) > ((2*max_chars)/3)) 
               or (miss_count < (max_misses-1) 
                   and len(cthis) > (max_chars/3) 
                   and len(cthat) > (max_chars/3) )
               ):
            retlist.append(k)
    return retlist

def process_fields(line,contest_votes_dict):
    """Given a csv line, enter the results in our dictionaries"""
    fa = line.split(",")
    LAYOUT = 1
    CONTEST = 3
    CHOICE = 4
    VOTEDTF = 26
    RED = 7
    #for num,field in enumerate(fa): print num,field

    # if variant is close to any merge dict keys, replace with merge dict value
    # otherwise, enter it into merge dict as its own value
    # increment count for variant if key exists, 
    # otherwise, see if this is a new entry for the merge dict;
    # if so, increment the resulting merged variant,
    # if not, enter the unmerged variant as a new key
    this_contest = fa[CONTEST]
    matches = is_this_like_them(this_contest,contest_merge_dict)
    if len(matches)>0:
        this_contest = contest_merge_dict[matches[0]]
    else:
        contest_merge_dict[this_contest] = this_contest
    # repeat process for choice
    this_choice = fa[CHOICE]
    matches = is_this_like_them(this_choice,choice_merge_dict)
    if len(matches)>0:
        this_choice = choice_merge_dict[matches[0]]
    else:
        choice_merge_dict[this_choice] = this_choice

    try:
        voteop_dict[(this_contest, this_choice)] += 1
    except:
        voteop_dict[(this_contest, this_choice)] = 1
    try:
        layout_voteop_dict[(fa[LAYOUT], this_contest, this_choice)] += 1
    except:
        layout_voteop_dict[(fa[LAYOUT], this_contest, this_choice)] = 1

    was_voted = (fa[VOTEDTF] == 'True')

    #red_intensity = fa[RED]

    if not was_voted: 
        return

    # update vote dictionaries, 
    # note that contest_votes_dict is per ballot 
    try:
        contest_votes_dict[this_contest] += 1
    except:
        contest_votes_dict[this_contest] = 1

    try:
        voted_dict[(this_contest, this_choice)] += 1
    except:
        voted_dict[(this_contest, this_choice)] = 1

    try:
        layout_voted_dict[(fa[LAYOUT], this_contest, this_choice)] += 1
    except:
        layout_voted_dict[(fa[LAYOUT], this_contest, this_choice)] = 1
    
def write_layout_count(out_file,k):
    try:
        choicecount = layout_voteop_dict[k]
    except KeyError:
        choicecount = 0
    try:
        votes = layout_voted_dict[k]
    except KeyError:
        votes = 0
    out_file.write("%06d,votes of,%06d,targets for layout,'%15s',%35s,%15s\n" % 
                   (votes,
                    choicecount,
                    k[0],
                    k[1][:35],
                    k[2][:15])
                   )

def write_count(out_file,k):
    try:
        choicecount = voteop_dict[k]
    except KeyError:
        choicecount = 0
    try:
        votes = voted_dict[k]
    except KeyError:
        votes = 0
    out_file.write("%06d,votes of,%06d,targets for,%35s,%15s\n" % 
                       (votes,
                        choicecount,
                        k[0][:35],
                        k[1][:15]))


def build_totals_from_results_files():
    """go to root/results as define in tevs.cfg, read all txts in all dirs"""
    resultsdir = const.root+"/results"
    dirlist = os.listdir(resultsdir)
    # filter results directory list to only 3 digit names
    dirlist = filter(lambda x: len(x)==3 , dirlist)
    dirlist.sort()
    dirlist = map(lambda x: resultsdir+"/"+x, dirlist)
    
    for num,d in enumerate(dirlist):
        print "Processing %d of %d: %s" % (num+1,len(dirlist),d)
        d2list = os.listdir(d)
        d2list.sort()
        d2list = map(lambda x: d+"/"+x,d2list)
        d2list = filter(lambda x: x.endswith('csv') or x.endswith('txt'),d2list)
        for fname in d2list:
            f = open(fname,"r")
            contest_votes_dict = {}
            lines = f.readlines()
            for l in lines:
                process_fields(l,contest_votes_dict)
            # maintain a dictionary of the number of times a ballot contributes
            # each number of votes to a contest, for determining overvote counts
            for k in contest_votes_dict:
                try:
                    votecount_counts_dict[(k,contest_votes_dict[k])] += 1
                except:
                    votecount_counts_dict[(k,contest_votes_dict[k])] = 1
        vklist = voted_dict.keys()
        vklist.sort()
        cklist = voteop_dict.keys()
        cklist.sort()
        lklist = layout_voted_dict.keys()
        lklist.sort()
        print len(cklist), "variants of offered contest/choice encountered."
        print len(vklist), "variants of voted contest/choice encountered."
        print len(lklist), "variants of voted layout/contest/choice encountered."

def to_spreadsheet(output_name,spread="/usr/bin/gnumeric"):
    try:
        pid = subprocess.Popen([spread,output_name]).pid
        print "Opening gnumeric on results file %s (%d)" % (output_name,pid)
    except OSError, e:
        print e
        print "Could not open %s. Is it installed?" % (spread,)

def output_totals_from_results_files():
    """ Output the various generated totals."""
    # output contest/choice name variants to contest/choice_names.csv
    for name,dict in (("contest_names.csv",contest_merge_dict),
                      ("choice_names.csv",choice_merge_dict)):
        out_file = open(name,"w")
        k = dict.keys()
        k.sort()
        for key in k:
            out_file.write("%s-->%s\n" % (key,dict[key]))

    vklist = voted_dict.keys()
    vklist.sort()
    cklist = voteop_dict.keys()
    cklist.sort()
    lklist = layout_voteop_dict.keys()
    lklist.sort()
    # output to summary.csv 
    #first all entries with 25 or more votes, then the stragglers
    output_name = "summary.csv"
    out_file = open(output_name,"w")
    for k in cklist:
        if voteop_dict[k]>=25: write_count(out_file, k)
    for k in cklist:
        if voteop_dict[k]<25: write_count(out_file, k)
    out_file.close()
    to_spreadsheet(output_name)

    # output to byprecinct.csv
    #first all entries with 5 or more votes, then the stragglers
    output_name = "byprecinct.csv"
    out_file = open(output_name,"w")
    for k in lklist:
        if layout_voteop_dict[k]>=5: write_layout_count(out_file,k)
    for k in lklist:
        if layout_voteop_dict[k]<5: write_layout_count(out_file,k)
    out_file.close()
    to_spreadsheet(output_name)

    # output to contest_votecount_counts.csv
    # Capture number of ballots with a particular vote count for each contest,
    # to determine potential overvote counts.
    vk = votecount_counts_dict.keys()
    vk.sort()
    output_name = "contest_votecount_counts.csv"
    out_file = open(output_name,"w")
    for k in vk:
        try:
            out_file.write("%06d,%02d,%60s\n" % (
                    votecount_counts_dict[k],
                    k[1],
                    k[0][:60])
                           )
        except:
            pdb.set_trace()
    to_spreadsheet(output_name)
        

def query_database(dbc):
    """ Submit several queries to the database, 
    getting the results into csv files.

    Start openoffice with each csv file as it is completed.
    """
    q, q1 = dbc.query, dbc.query1

    num_vops = q1("select count(was_voted) from voteops")[0]
    print "Vote opportunities: %d" % (num_vops,)
    num_voted = q1("select count(was_voted) from voteops where was_voted")[0]
    print "VOTED vote opportunities: %d" % (num_voted,)

    # ELECTION WIDE

    for query in queries:
        print "Now getting %s results." % (query[2],)
        if num_voted > 1000000:
            print "Next output may take several minutes."
        elif num_voted > 100000:
            print "Next output may take a minute."
        result = dbc.query(query[0])
        lastrecord1 = ""
        out_file = open(query[1],"w")
        for record in result:
            if record[1]<>lastrecord1:
                lastrecord1 = record[1]
            for field in record:
                out_file.write(str(field))
                out_file.write(",")
            out_file.write("\n")
        out_file.close()
        to_spreadsheet(query[1])

    del q #bad form, but acceptable here, for simplicity's sake
    del q1
    return locals()

def main():
    global log
    cfg_file = "tevs.cfg"
    out_file = open("summary.csv","w")
    config.get(cfg_file)
    log = config.logger(util.root("log.txt"))

    #pdb.set_trace()
    #matches = is_this_like_them("hello there",{"hellc there":"bonjour","yabba":"dabba"})

    if not const.use_db:
        print "The configuration file indicates no database is in use."
        print "We will now build totals from the results files."
        build_totals_from_results_files()
        output_totals_from_results_files()
        return 0

    try:
        dbc = db.PostgresDB(const.dbname, const.dbuser)
        print "Generating totals from db %s, user %s" % (const.dbname, 
                                                         const.dbuser)
        print "If there are many vote ops, this may take several minutes."
        print "The next output will be the number of vote opportunities."
        qs = query_database(dbc)
    except db.DatabaseError:
        print "Although the configuration file indicates a database is in use,"
        print "we could not connect for dbname %s user %s." % (const.dbname, 
                                                               const.dbuser)
        print "We will now build totals from the results files."
        build_totals_from_results_files()
        output_totals_from_results_files()
        return 0

    return 0
    
if __name__ == '__main__':
    rc = main()
    sys.exit(rc)
