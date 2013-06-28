#!/bin/env python

# This script reads an obfuscated decimal number (as read from the bar code)
# from standard input, and reads out the corresponding selected votes.
# If a Cue Cat (or other bar code reader that is connected to the keyboard)
# is used, then just start the program and scan.
# 
# Edit 'command' below to specify the command used for playing wav files.

import os, sys, re, time
sys.path.append(os.path.join('..', '..'))
from evm2003.utils.convert import digits2votes
from getpass import getpass

command = "play"
#command = "qtplay -q"
#command = "WAV.EXE"

length = [8, 8, 3, 3, 4, 3, 4, 3, 2, 2, 2, 10, 64]

if command == "WAV.EXE":
    extra = " /Q"
else:
    extra = ""
text = {}
texts = open("texts")
for line in texts.readlines():
    (key, text[key + ".WAV"]) = line.split("\t")

try:
    while 1:
        scan = getpass('Ready...')
        fields = re.split(";", scan)
        digits = fields.pop(0)
        if re.match(r'\d{40}$', digits):
            votes = digits2votes(digits)
            ncand = 2
            if votes != []:
                files = []
                offset = 0
                for i in range(len(votes)):
                    if votes[i] == 0 or votes[i] == []:
                        files += ["NP%.2d" % (i+1) + ".WAV"]
                    elif i < 11:
                        file = "SEL%.3d" % (offset+votes[i]) + ".WAV"
                        files += [file]
                        if re.search("write-in", text[file], re.I):
                            for k in range(ncand):
                                name = fields.pop(0)
                                text[file] += "\n  " + name
                                for char in name:
                                    spell = os.path.join('..', 'rii/audio/Spell' + str(ord(char.upper())) + '.wav')
                                    files += [spell]
                                    text[spell] = ''
                                if i == 0 and k == 0:
                                    files += ["pause"]
                                    text["pause"] = ''
                    else:
                        for j in range(len(votes[i])):
                            if i == 11:
                                file = "SEL%.3d" % (offset+votes[i][j]) + ".WAV"
                                files += [file]
                            else:
                                file = "SEL%.3d" % (offset+8*votes[i][j]-7+j) + ".WAV"
                                files += [file]
                            if re.search("write-in", text[file], re.I):
                                for k in range(ncand):
                                    name = fields.pop(0)
                                    text[file] += "\n  " + name
                                    for char in name:
                                        spell = os.path.join('..', 'rii/audio/Spell' + str(ord(char.upper())) + '.wav')
                                        files += [spell]
                                        text[spell] = ''
                    offset += length[i]
                    ncand = 1
                print
                for file in files:
                    if text[file] != '':
                        print text[file]
                        print "\n\n\n",
                    if file == "pause":
                        time.sleep(1.5)
                    else:
                        os.system("%s %s" % (command, file + extra))
            else:
                print "Invalid vote"
        else:
            print "Invalid vote"

except KeyboardInterrupt:
    pass
