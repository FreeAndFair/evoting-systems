#!/bin/env python

# This script prints a ballot as PostScript to the file ballot.ps.
# Indata comes from the file vote-selection.xml.

import sys
if sys.platform != 'win32':
    sys.path.append('../..')
else:
    sys.path.append('..\\..')
from evm2003.Print.PaperBallot import PaperBallot

p = PaperBallot("vote-selection.xml")
p.PostscriptPrint("ballot.ps")
del p
