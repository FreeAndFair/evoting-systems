#!/bin/env python

import sys, random
from RII import RII

country = "US"
State = "CA"
county = "Santa Clara County"
precinct = 2216
date = 20081104
serial = 213
machine_id = 4
session_ids = range(1000)
random.shuffle(session_ids)
textmode = sys.argv.count('-t')
printps = not sys.argv.count('-p')
debug = sys.argv.count('-d')
quick = sys.argv.count('-q')
v = RII()
while v.main(country, State, county, precinct, date, machine_id, serial,
             session_ids, textmode, printps, debug, quick):
    pass
