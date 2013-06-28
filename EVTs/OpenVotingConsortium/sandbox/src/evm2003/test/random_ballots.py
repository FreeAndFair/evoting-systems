#!/usr/bin/env python
from evm2003.data.contests import cont as _
import random, sys, os

date="2004-11-04"
country="US"
state="CA"
county="Santa Clara County"
precinct="2216"
ids = range(10000)
random.shuffle(ids)
serial="213"

OUT = sys.stdout

def pr(pat, val=None):
    if val is None:
        print >> OUT, pat
    else:
        val = val or "No preference indicated"
        print >> OUT, pat % val

def make_ballots(count):
    global OUT
    filenames = []
    for i in range(count):
        filename = "v-%s-%s-%s-%s-%s-%04d.xml" %\
          (date.replace("-",""), country, state,
           county.replace(" ","_"), precinct, ids[i])
        OUT = open(filename,'w')
        filenames.append(filename)

        pr('<?xml version="1.0" encoding="UTF-8"?>')
        pr('''<cast_ballot election_date="%s" country="%s" state="%s"
             county="%s" number="%s" precinct="%s"
             serial="%s" source="voting_machine">''',
           (date, country, state, county, ids[i], precinct, serial))
        pr('  <contest ordered="No" coupled="Yes" name="Presidency">')
        prez = random.choice(_['Presidency'])
        pr('    <selection writein="No" name="President">%s</selection>',prez[0])
        pr('    <selection writein="No" name="Vice President">%s</selection>',prez[1])
        pr('  </contest>')
        single_pick = ('Senator', 'U.S. Representative', 'Treasurer',
            'Attorney General', 'Commis. of Education', 'State Senate',
            'State Assembly', 'Transportation Initiative',
            'Health care initiative', 'Term limits')
        for contest in single_pick:
            pr('  <contest ordered="No" coupled="No" name="%s">', contest)
            choice = random.choice(_[contest])
            pr('    <selection writein="No">%s</selection>',choice)
            pr('  </contest>')
        for multi in (("Cat Catcher",3,"No"),("County Commissioner",8,"Yes")):
            pr('  <contest ordered="%s" coupled="No" name="%s">',(multi[2],multi[0]))
            random.shuffle(_[multi[0]])
            for n in range(random.randrange(multi[1])):
                vote = _[multi[0]][n]
                if not vote:
                    pr('    <selection writein="Yes">WRITE-IN</selection>')
                else:
                    pr('    <selection writein="No">%s</selection>', vote)
            else:
                pr('    <selection>No preference indicated</selection>')
            pr('  </contest>')
        pr('</cast_ballot>')
        OUT.close()
    return filenames

if __name__=='__main__':
    if len(sys.argv) >= 2:
        num = int(sys.argv[1])
        assert num <= 10000
        fnames = make_ballots(num)
        if len(sys.argv) > 2 and sys.argv[2] in ('-ps', '--postscript'):
            from evm2003.Print.PaperBallot import xml2ps, PaperBallot
            for fname in fnames:
                psname = fname.replace('.xml','.ps')
                xml2ps(fname, psname)
    else:
        print "Please specify the number of ballots to generate."
        print "(for postscript use: random_ballots.py NUM -ps)"

