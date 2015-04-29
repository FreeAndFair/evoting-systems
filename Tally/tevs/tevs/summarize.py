#!/usr/bin/env python
import sys
#import argparse
import pdb
import db
import config
import const #XXX tbd
import util

console_template = """
Election-wide results:
    {election_wide}

Election-wide results by layout code:
    {election_wide_by_layoutcode}

Election-wide results by layout code sorted by contest:
    {election_wide_by_layoutcode_sorted_by_contest}

Election-wide voted results:
    {election_wide_voted}

Election-wide voted results by layout code:
    {election_wide_voted_by_layoutcode}

Election-wide voted results by layout code sorted by contest:
    {election_wide_voted_by_layoutcode_sorted_by_contest}


Total voted boxes:\t{num_voted}
Total unvoted boxes:\t{num_non_voted}
Total bad voted areas:\t{num_bad}
"""[1:] #get rid of \n after the quotes on top, bottom \n needed
def console_display(data):
    def fmt1(key, template):
        data[key] = "\n\t".join(template.format(*d) for d in data[key])
    #: #, con, cho 
    fmt1("election_wide", 
        "{1},{2},{0}"
    )
    #: #, code, con, cho 
    fmt1("election_wide_by_layoutcode", 
        "{1},{2},{3},{0}"
    )
    #: #, code, con, cho
    fmt1("election_wide_by_layoutcode_sorted_by_contest",
        "{1},{2},{3},{0}"
    )

    fmt1("election_wide_voted", 
        "{1},{2},{0}"
    )
    fmt1("election_wide_voted_by_layoutcode", 
        "{1},{2},{3},{0}"
    ) 
    fmt1("election_wide_voted_by_layoutcode_sorted_by_contest",
        "{1},{2},{3},{0}"
    )

    return console_template.format(**data)

display = {
    "console": console_display,
}

def query(dbc,out_file):
    q, q1 = dbc.query, dbc.query1

    num_vops = q1("select count(was_voted) from voteops")[0]
    num_voted = q1("select count(was_voted) from voteops where was_voted")[0]
    num_bad = q1("select count(original_x) from voteops where original_x = -1")[0]
    num_non_voted = num_vops - num_voted

    #total
    election_wide = q(
    """select count(contest_text), contest_text, choice_text
        from voteops
        group by contest_text, choice_text
        order by contest_text, choice_text
        ;"""
    )
    lastrecord1 = ""
    for record in election_wide:
        if record[1]<>lastrecord1:
            print record[1]
            lastrecord1 = record[1]
        out_file.write("%05d,%30s,%30s\n" % (record[0],record[2][:30],record[1][:30]))
    out_file.close()
    pdb.set_trace()
    election_wide_by_layoutcode = q(
    """select count(code_string), code_string, contest_text, choice_text
        from voteops join ballots on voteops.ballot_id = ballots.ballot_id
        group by code_string, contest_text, choice_text
        order by code_string
        ;"""
    )
    election_wide_by_layoutcode_sorted_by_contest = q(
    """select count(code_string), code_string, contest_text, choice_text
        from voteops join ballots on voteops.ballot_id = ballots.ballot_id
        group by contest_text, choice_text, code_string
        order by contest_text, choice_text
        ;"""
    )

    #voted
    election_wide_voted = q(
    """select count(contest_text), contest_text, choice_text
        from voteops where was_voted
        group by contest_text, choice_text
        order by choice_text
        ;"""
    )
    election_wide_voted_by_layoutcode = q(
    """select count(code_string), code_string, contest_text, choice_text
        from voteops join ballots on voteops.ballot_id = ballots.ballot_id
        where was_voted
        group by code_string, contest_text, choice_text
        order by code_string
        ;"""
    )
    election_wide_voted_by_layoutcode_sorted_by_contest = q(
    """select count(code_string), code_string, contest_text, choice_text
        from voteops join ballots on voteops.ballot_id = ballots.ballot_id
        where was_voted
        group by contest_text, choice_text, code_string
        order by contest_text, choice_text
        ;"""
    )


    del q #bad form, but acceptable here, for simplicity's sake
    del q1
    return locals()

#flags = argparse.ArgumentParser(
#    description='Summarize ballot counts from database',
#)
#flags.add_argument('-c', '--config', dest="cfg")

def main():
    cfg_file = "tevs.cfg"
    out_file = open("summary.csv","w")
    config.get(cfg_file)

    log = config.logger(util.root("log.txt"))
    if not const.use_db:
        log.error("Cannot summarize database without a database")
        return 1

    try:
        dbc = db.PostgresDB(const.dbname, const.dbuser)
        print "preparing summary for", const.dbname, "user", const.dbuser
    except db.DatabaseError:
        log.error("Could not connect to database")
        return 2

    qs = query(dbc,out_file)
    pdb.set_trace()
    printer = display['console']
    print printer(qs)

    return 0
    
if __name__ == '__main__':
    #args = flags.parse_args()
    rc = main()
    sys.exit(rc)
