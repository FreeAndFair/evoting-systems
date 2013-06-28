#!/bin/env python

import sys
if sys.platform != 'win32':
    sys.path.append('../..')
else:
    sys.path.append('..\\..')
from evm2003.utils.convert import digits2votes
from evm2003.utils.getxml import ballotxml

country = "US"
state = "CA"
county = "Santa Clara County"
ballot_number = 1234
precinct = 2216
date = 20041104
barcode = "4098429771589485355423334452689650248916"
writeins = [['', ''], '', '', '', '', '', '', '', '', '', '', '', '']
votes = digits2votes(barcode)
xml = ballotxml(date, country, state, county, ballot_number, precinct, "", "scan", votes, writeins)
print xml
