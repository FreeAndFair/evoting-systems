#!/bin/env python

# This script reads an obfuscated decimal number (as read from the bar code)
# from standard input, and reads out the corresponding selected votes.
# If a Cue Cat (or other bar code reader that is connected to the keyboard)
# is used, then just start the program and scan.
# 
# Edit 'command' and 'dir' below to specify the command used for playing
# wav files, and the directory containing the audio files, respectively.


import os
from evm2003.bva.Play import Play
from evm2003.utils.convert import digits2votes
from getpass import getpass

command = "play"
dir = "/home/jan/voting-project/wav/"

while 1:
#    digits = raw_input('Ready...')
    digits = getpass('Ready...')
    votes = digits2votes(digits)
    if votes != []:
        os.write(1, "\n\nPlaying...")
        Play(votes, command, dir)
        print "\n\n\n",
    else:
        print "Invalid vote"
