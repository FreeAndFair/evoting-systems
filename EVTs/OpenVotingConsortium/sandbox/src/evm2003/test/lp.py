#!/bin/env python

# This script prints a ballot as PostScript to a printer. Modify the print
# command and printer queue below to reflect your local environment.
# Indata comes from the file vote-selection.xml.

import os, sys
if sys.platform != 'win32':
    sys.path.append('../..')
else:
    sys.path.append('..\\..')
from evm2003.Print.PaperBallot import PaperBallot

p = PaperBallot("vote-selection.xml")

try:
    lp = os.popen("/bin/lp -d pr4118a", "w")
    lp.write(p.GetPostScript())
    lp.close()
except (IOError, EOFError), e:
    print e

del p
