# -*- coding: iso-8859-1 -*-
import os, sys, signal, time, select, re
platform = sys.platform
if platform != 'win32':
    import curses
else:
    import msvcrt, win32api, win32process, winsound
sys.path.append(os.path.join('..', '..'))
from evm2003.Print.PaperBallot import PaperBallot
from evm2003.utils.getxml import ballotxml
from evm2003.data.contests import cont

printcommand = "/usr/bin/lpr"

STATE_INIT = 0
STATE_FOLDER = 1
STATE_INTRO = 2
STATE_CONTEST = 3
STATE_SELECT = 4
STATE_WRITEINQ = 5
STATE_WRITEIN1 = 6
STATE_WRITEIN2 = 7
STATE_WRITEINC = 8
STATE_CONFIRM = 9
KEY_HELP = 27         # Use Esc key for help
if platform != "win32":
    KEY_BACKSPACE = curses.KEY_BACKSPACE
    KEY_LEFT = curses.KEY_LEFT
    KEY_RIGHT = curses.KEY_RIGHT
    KEY_UP = curses.KEY_UP
    KEY_DOWN = curses.KEY_DOWN
else:
    KEY_BACKSPACE = 263
    KEY_LEFT = 260
    KEY_RIGHT = 261
    KEY_UP = 259
    KEY_DOWN = 258

if platform == 'cygwin' or platform == 'win32':
    audiodir = "audio\\"
else:
    audiodir = "audio/"

class RII(object):
    """Reading Impaired Interface

    An interface intended for reading impaired voters that have the ability to

    - Hear and understand spoken instructions
    - Use the arrow and escape keys on a standard 101 PC keyboard
    - Pick up a piece of paper from the printer and place the paper in
      a privacy folder

    The voter navigates through the ballot using the arrow keys, following
    instructions given through headphones. The implementation has a number
    of methods that are called after each valid key-press. Which method that
    is to be called depends on which key is pressed, and what the current state
    in the voting process is. There are nine different states, defined by the
    constants above. For example, if in the candidate selection state (the
    slow list), and the voter selects a candidate by pressing the down arrow
    key - then the select_down() method is called.

    Version: 1.1
    Author:  Jan Kärrman
    Date:    Jan 8 2004
    """

# Get text to be shown together with the corresponding audio
    text = {}
    new = 1
    texts = open("texts")
    for line in texts.readlines():
        if line == "-" * 55 + "\n":
            text[key] = value
            new = 1
        elif new:
            key = line.split("\n")[0].split(" ")[0]
            value = ""
            new = 0
        else:
            value += line
    texts.close()

# Valid characters to use for write-ins
    chars = range(65,91) + [32, 39, 45, 46]
    valid = [0] * 512
    for c in chars + range(97,123):
        valid[c] = 1
    valid[KEY_BACKSPACE] = 1
    valid[8] = 1
    valid[10] = 1
    valid[13] = 1

    length = [8, 8, 3, 3, 4, 3, 4, 3, 2, 2, 2, 10, 8]
    writein = [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1]

    wait = 3
    state = STATE_INIT

    def d(self, s):
        """Use for debugging"""
        if platform != "win32":
            self.stdscr.move(22, 0)
            self.stdscr.clrtoeol()
        self.addstr(str(s))
        if platform != "win32": self.stdscr.refresh()
        time.sleep(1)

    def stopaudio(self):
        """Stop the audio if still running"""
#        print '--- '+str(self.handle)
        if platform != "win32":
            if self.pid != 0:
                try:
                    os.kill(self.pid, signal.SIGTERM)
                    os.waitpid(self.pid, 0)
                except OSError:
                    pass
        else:
            try:
                win32api.TerminateProcess(self.handle, 0)
                os.waitpid(self.handle, 0)
            except:
                pass

    def running(self):
        """Check if the audio is still running"""
        if platform != "win32":
            try:
                os.kill(self.pid, 0)
                os.waitpid(self.pid, os.WNOHANG)
                return 1
            except OSError:
                return 0
        else:
            try:
                win32api.OpenProcess(1, 0, self.pid)
                return 1
            except:
                return 0

    def key_pressed(self):
        """Check if a key has been pressed"""
        if platform != "win32":
            return select.select([0], [], [], 0)[0]
        else:
            return msvcrt.kbhit()

    def play(self, file, mode, delay, sleep1, flush, sleep2):
        """Play an audio file, and write the corresponding text on screen

        Parameters:
            file:   The audio file to play
            mode:   os.P_WAIT or os.P_NOWAIT (interruptible)
            delay:  Number of seconds to wait after the audio has finished
                    and no key has been pressed (selection timeout)
            sleep1: Number of seconds to sleep after the audio has finished
            flush:  Flush typeahead characters from the input buffer
            sleep2: Number of seconds to sleep when in text-only mode
        """

#        if platform != "win32":
#            self.stdscr.move(2, 0)
#            self.stdscr.clrtobot()
        self.mode = mode
        self.delay = delay
        self.addstr(file + ":  " + self.text[file], 4, 0)
        if platform != "win32":
            self.stdscr.clrtobot()
            self.stdscr.refresh()
        file = audiodir + file
        if not self.textmode and os.path.isfile(file):
            if platform == "win32":
                try:
                    win32api.CloseHandle(self.handle)
                except:
                    pass
                self.handle, ht, self.pid, t = win32process.CreateProcess("WAV.EXE",
                                    "WAV " + file + " /Q", None, None, False,
                                    win32process.DETACHED_PROCESS, None, None,
                                    win32process.STARTUPINFO())
                if mode == os.P_WAIT: os.waitpid(self.handle, 0)
            elif platform == "cygwin":
                self.pid = os.spawnl(mode, "WAV.EXE", "WAV", file, "/Q")
            else:
#                self.pid = os.spawnl(mode, "/usr/local/bin/qtplay", "qtplay", file)
                self.pid = os.spawnl(mode, "/usr/bin/sox", "sox", file,
                                "-t", "ossdsp", "/dev/dsp")
#                self.pid = os.spawnl(mode, "/it/sw/audio/bin/sox", "sox", file,
#                                "-t", "sunau", "/dev/audio")
            time.sleep(sleep1)
        else:
            self.pid = 0
            time.sleep(sleep2)
        if flush: self.flushinp()

    def flushinp(self):
        if platform != "win32":
            curses.flushinp()
        else:
            while msvcrt.kbhit():
                msvcrt.getch()

    def pcont(self, w1, w2):
        """Play contest info. Use short version if already visited."""
        if self.visited[self.contest]:
            self.play("Cont1%.2d.wav" % self.contest, os.P_NOWAIT, w1, 0, 1, w2)
        else:
            self.visited[self.contest] = 1
            self.play("Cont0%.2d.wav" % self.contest, os.P_NOWAIT, w1, 0, 1, w2)

    def spellout(self, string):
        """Spell out text, given in string"""
        for cha in list(string):
            ch = ord(cha)
            if ch > 96 and ch < 123: ch -= 32
            self.play("Spell%.2d.wav" % ch, os.P_WAIT, 0, 0.3, 0, 1)

    def done(self):
        """Play back all selections"""
        if self.quick: return
        time.sleep(1)
        for i in range(len(self.sel)):
            if self.sel[i] == 0 or self.sel[i] == []:
                self.play("NP%.2d.wav" % i, os.P_WAIT, 0, 0, 0, 2)
            elif i == 0:
                if self.sel[0] == self.length[0]:
                    self.play("Writes.wav", os.P_WAIT, 0, 0.5, 0, 1)
                    self.play("Pres1.wav", os.P_WAIT, 0, 0, 0, 1)
                    self.spellout(self.writeins[0][0])
                    self.play("Pres2.wav", os.P_WAIT, 0, 0, 0, 1)
                    self.spellout(self.writeins[0][1])
                else:
                    self.play("Cand00%d.wav" % (self.sel[0]-1), os.P_WAIT, 0, 0, 0, 1)
            elif i < 11:
                self.play("Cont2%.2d.wav" % i, os.P_WAIT, 0, 0.5, 0, 1)
                if self.sel[i] == self.length[i] and self.writein[i]:
                    self.play("Write.wav", os.P_WAIT, 0, 0.5, 0, 1)
                    self.spellout(self.writeins[i])
                else:
                    self.play("Cand%.2d%d.wav" % (i, self.sel[i]-1), os.P_WAIT, 0, 0, 0, 1)
            else:
                self.play("Cont2%.2d.wav" % i, os.P_WAIT, 0, .5, 0, 1)
                for j in range(len(self.sel[i])):
                    if i == 12 and j == 0 and len(self.sel[i]) > 1:
                        self.play("Rank.wav", os.P_WAIT, 0, .5, 0, 1)
                    if self.sel[i][j] == self.length[i]:
                        self.play("Write.wav", os.P_WAIT, 0, 0, 0, 1)
                        self.spellout(self.writeins[i])
                    else:
                        self.play("Cand%.2d%d.wav" % (i, self.sel[i][j]-1), os.P_WAIT, 0, 0, 0, 1)
            time.sleep(1)

    def getch(self):
        if platform != "win32":
            return self.stdscr.getch()
        else:
            c = ord(msvcrt.getch())
            if c == 224:
                c = ord(msvcrt.getch())
                if c == 75: c = KEY_LEFT
                if c == 77: c = KEY_RIGHT
                if c == 72: c = KEY_UP
                if c == 80: c = KEY_DOWN
            return c

    def addstr(self, string, *pos):
        if platform != "win32":
            if pos:
                self.stdscr.addstr(pos[0], pos[1], string)
            else:
                self.stdscr.addstr(string)
        else:
            print string

    def beep(self):
        if platform != "win32":
            curses.beep()
        else:
            winsound.Beep(3000,60)

    def init_down(self):
        """Go to the introduction"""
        self.play("Intro1.wav", os.P_NOWAIT, 1, 0, 0, 0)
        self.state = STATE_FOLDER

    def init_help(self):
        self.play("Start.wav", os.P_WAIT, 0, 0, 0, 1)

    def folder_down(self):
        """Go to the contests"""
        self.play("Intro2.wav", os.P_NOWAIT, 1, 0, 0, 1)
        self.state = STATE_INTRO

    def folder_help(self):
        self.play("Intro1.wav", os.P_NOWAIT, 1, 0, 0, 1)

    def intro_down(self):
        """Go to the contests"""
        self.pcont(0, 1)
        self.state = STATE_CONTEST

    def intro_help(self):
        self.play("Intro2.wav", os.P_NOWAIT, 1, 0, 0, 1)

    def contest_left(self):
        """Go to previous contest"""
# Don't wrap around until all contests have been visited
        if self.contest > 0 or self.confirm == 1:
            self.contest = (self.contest - 1) % 13
            self.pcont(0, 1)
        else:
            self.beep()
        self.state = STATE_CONTEST

    def contest_right(self):
        """Go to next contest"""
        if self.contest == 12 and not self.confirm:
            self.play("Done1.wav", os.P_WAIT, 0, 0, 0, 2)
            self.done()
            self.play("Done3.wav", os.P_NOWAIT, 0, 0, 1, 0)
            self.confirm = 1
            self.state = STATE_CONFIRM
        else:
            self.contest = (self.contest + 1) % 13
            self.pcont(0, 1)
            self.state = STATE_CONTEST

    def contest_up(self):
        if self.confirm:
            self.play("Done2.wav", os.P_NOWAIT, 0, 0, 1, 1)
            self.state = STATE_CONFIRM
        else:
            self.play("Intro2.wav", os.P_NOWAIT, 1, 0, 0, 0)
            self.state = STATE_INTRO

    def contest_down(self):
        """Start selection mode (slow list)"""
        if self.contest == 12:
            self.play("Rank1.wav", os.P_WAIT, 0, 1, 0, 2)
        self.cand = 0
        self.selected = 0
        if self.contest < 11:
            self.sel[self.contest] = 0
        else:
            self.sel[self.contest] = []
        self.rank = 1
        self.ranked = [0] * 8
        self.play("Cand%.2d0.wav" % self.contest, os.P_WAIT, self.wait, 0, 0, 0)
        self.string = ""
        self.state = STATE_SELECT

    def contest_help(self):
        self.play("Cont0%.2d.wav" % self.contest, os.P_NOWAIT, 0, 0, 0, 1)

    def select_left(self):
        """Abort selection, and go to previous contest"""
        if self.confirm:
            self.play("Done2.wav", os.P_NOWAIT, 0, 0, 1, 1)
            self.state = STATE_CONFIRM
        else:
            self.contest_left()

    def select_right(self):
        """Abort selection, and go to next contest"""
        if self.confirm:
            self.play("Done2.wav", os.P_NOWAIT, 0, 0, 1, 1)
            self.state = STATE_CONFIRM
        else:
            self.contest_right()

    def select_up(self):
        """Abort selection"""
        if self.confirm:
            self.play("Done2.wav", os.P_NOWAIT, 0, 0, 1, 1)
            self.state = STATE_CONFIRM
        else:
            self.pcont(0, 1)
            self.state = STATE_CONTEST

    def select_down(self):
        """Select a candidate"""
        if self.cand != self.length[self.contest] - 1 or not self.writein[self.contest]:
# A regular candidate
            self.play("Select.wav", os.P_WAIT, 0, 0, 0, 1)
            self.play("Cand%.2d%.1d.wav" % (self.contest, self.cand), os.P_WAIT, self.wait, 1, 0, 2)
            if self.contest < 11:
                self.sel[self.contest] = self.cand + 1
                if self.confirm:
                    self.play("Done2.wav", os.P_NOWAIT, 0, 0, 1, 1)
                    self.state = STATE_CONFIRM
                else:
                    self.contest = (self.contest + 1) % 13
                    self.pcont(0, self.wait)
                    self.visited[self.contest] = 1
                    self.state = STATE_CONTEST
            elif self.contest == 11:
# Cat catcher
                self.sel[self.contest].append(self.cand + 1)
                if self.selected < 2 and self.cand < self.length[self.contest]-1:
                    self.play("More%d.wav" % (2-self.selected), os.P_WAIT, self.wait, .5, 0, 1)
                    self.cand += 1
                    self.play("Cand%.2d%.1d.wav" % (self.contest, self.cand), os.P_WAIT, self.wait, 0, 0, 0)
                else:
                    self.state = STATE_CONTEST
                    if self.confirm:
                        self.play("Done2.wav", os.P_NOWAIT, 0, 0, 1, 1)
                        self.state = STATE_CONFIRM
                    else:
                        self.contest = (self.contest + 1) % 13
                        self.pcont(0, self.wait)
                        self.visited[self.contest] = 1
            else:
# County Commisioner
                self.sel[self.contest].append(self.cand + 1)
                self.next_nofm()
            self.selected += 1
            self.wrotein = 0
        else:
# A wite-in candidate
            if self.skill == 0:
# Ask (once) about keyboard skill
                self.play("Writein.wav", os.P_NOWAIT, 0, 0, 0, 1)
                self.state = STATE_WRITEINQ
            elif self.skill == 1:
                self.play("Arrows%.1d.wav" % self.told, os.P_NOWAIT, 0, 0, 0, 1)
                self.state = STATE_WRITEIN1
            else:
                self.play("Type.wav", os.P_NOWAIT, 0, 0, 0, 0)
                self.state = STATE_WRITEIN2
            self.string = ""
            self.wrotein = 0
            self.char = -1

    def select_timeout(self):
        """No key was pressed within the specified time"""
        if self.cand < self.length[self.contest]-1:
            if self.contest <= 11:
                self.cand += 1
                self.play("Cand%.2d%.1d.wav" % (self.contest, self.cand), os.P_WAIT, self.wait, 0, 0, 0)
            else:
                self.cand += 1
                while self.cand < self.length[self.contest] and self.ranked[self.cand] == 1:
                    self.cand += 1
                if self.cand < self.length[self.contest]:
                    self.play("Cand%.2d%.1d.wav" % (self.contest, self.cand), os.P_WAIT, self.wait, 0, 0, 0)
        else:
            if self.selected == 0:
                self.play("NP%.2d.wav" % self.contest, os.P_WAIT, 0, 0, 0, 2)
            if self.contest == 12 and self.confirm == 0:
                self.play("Done1.wav", os.P_WAIT, 0, 0, 0, 2)
                self.done()
                self.play("Done3.wav", os.P_NOWAIT, 0, 0, 0, 0)
                self.confirm = 1
                self.state = STATE_CONFIRM
            elif self.confirm:
                self.play("Done2.wav", os.P_NOWAIT, 0, 0, 1, 1)
                self.state = STATE_CONFIRM
            else:
                self.contest = (self.contest + 1) % 13
                self.pcont(0, self.wait)
                self.visited[self.contest] = 1
                self.state = STATE_CONTEST

    def select_help(self):
        self.play("Helpselect.wav", os.P_NOWAIT, 0, 0, 0, 1)

    def writeinq_right(self):
        """The voter has chosen to use the keyboard for write-ins"""
        self.play("Type.wav", os.P_NOWAIT, 0, 0, 0, 1)
        self.skill = 2
        self.state = STATE_WRITEIN2

    def writeinq_down(self):
        """The voter has chosen to use the arrow keys for write-ins"""
        self.play("Arrows%.1d.wav" % self.told, os.P_NOWAIT, 0, 0, 0, 1)
        self.told = 1
        self.skill = 1
        self.state = STATE_WRITEIN1

    def writeinq_help(self):
        self.play("Writein.wav", os.P_NOWAIT, 0, 0, 0, 1)

    def writein1_left(self):
        """Play previous character"""
        char = self.char
        if char > 0:
            char = (char - 1) % len(self.chars)
        else:
            char = len(self.chars) - 1
        self.play("Char%.2d.wav" % self.chars[char], os.P_WAIT, 0, 0, 0, 0)
        self.char = char

    def writein1_right(self):
        """Play next character"""
        char = self.char
        char = (char + 1) % len(self.chars)
        self.play("Char%.2d.wav" % self.chars[char], os.P_WAIT, 0, 0, 0, 0)
        self.char = char

    def writein1_up(self):
        """Erase last character"""
        if len(self.string) > 0:
            if ord(self.string[-1]) > 64:
                self.play("Del.wav", os.P_WAIT, 0, 0, 0, .5)
                self.play("Char%.2d.wav" % ord(self.string[-1]), os.P_WAIT, 0, 0, 0, 0)
            else:
                self.play("Del%.2d.wav" % ord(self.string[-1]), os.P_WAIT, 0, 0, 0, 0)
            self.string = self.string[:-1]
            if platform != "win32": self.stdscr.move(3, 0)
            self.addstr(self.string)
            if platform != "win32":
                self.stdscr.refresh()
                self.stdscr.clrtoeol()
        else:
            self.beep()
        self.char = -1

    def writein1_down(self):
        """Select current character, or finish writing if no character"""
        char = self.char
        if len(self.string) < 40 and char >= 0:
            self.string += chr(self.chars[char])
            if self.chars[char] > 64:
                self.play("Ins.wav", os.P_WAIT, 0, 0, 0, .5)
                self.play("Char%.2d.wav" % self.chars[char], os.P_WAIT, 0, 0, 0, 0)
            else:
                self.play("Ins%.2d.wav" % self.chars[char], os.P_WAIT, 0, 0, 0, 0)
            self.char = -1
        else:
            self.wconf()
        if platform != "win32":
            self.stdscr.move(3, 0)
            self.stdscr.clrtoeol()
        self.addstr(self.string)
        if platform != "win32": self.stdscr.refresh()

    def writein1_plus(self):
        self.skill = 2
        self.state = STATE_WRITEIN2

    def writein1_help(self):
        self.play("Arrows0.wav", os.P_NOWAIT, 0, 0, 0, 1)

    def writein2_down(self):
        """Finish writing, and request confirmation"""
        self.wconf()

    def writein2_type(self):
        """Insert/remove characters. Request confirmation if <Enter>"""
        char = self.char
        if self.c == KEY_BACKSPACE or self.c == 8:
            if len(self.string) > 0:
                char = ord(self.string[-1])
                self.string = self.string[:-1]
                if char > 96 and char < 123: char -= 32
                if char > 64:
                    self.play("Del.wav", os.P_WAIT, 0, 0, 0, .5)
                    self.play("Char%.2d.wav" % char, os.P_WAIT, 0, 0, 0, 0)
                else:
                    self.play("Del%.2d.wav" % char, os.P_WAIT, 0, 0, 0, 0)
            else:
                self.beep()
        elif self.c == 10 or self.c == 13:
            self.wconf()
        else:
            self.string += chr(self.c)
            if self.c > 96 and self.c < 123: self.c -= 32
            self.play("Char%.2d.wav" % self.c, os.P_WAIT, 0, 0, 0, 0)
        if platform != "win32":
            self.stdscr.move(3, 0)
            self.stdscr.clrtoeol()
        self.addstr(self.string)
        if platform != "win32": self.stdscr.refresh()

    def writein2_help(self):
        self.play("Type.wav", os.P_NOWAIT, 0, 0, 0, 1)

    def writeinc_left(self):
        """Replace write-in"""
        if self.skill == 1:
            self.play("Arrows%.1d.wav" % self.told, os.P_NOWAIT, 0, 0, 0, 0)
            self.state = STATE_WRITEIN1
        else:
            self.play("Type.wav", os.P_NOWAIT, 0, 0, 0, 0)
            self.state = STATE_WRITEIN2
        self.string = ""

    def writeinc_down(self):
        """Write-in accepted"""
        if len(self.string) > 0:
            if self.contest == 0:
                self.writeins[0][self.wrotein] = self.string
            else:
                self.writeins[self.contest] = self.string
            if self.contest < 11:
                self.sel[self.contest] = self.cand + 1
            else:
                self.sel[self.contest].append(self.cand + 1)
            if self.wrotein == 0 and self.contest == 0:
                self.play("Vice.wav", os.P_WAIT, 0, 0, 0, 1)
                self.string = ""
                if self.skill == 1:
                    self.state = STATE_WRITEIN1
                else:
                    self.state = STATE_WRITEIN2
            elif self.contest < 12:
                self.contest_right()
            else:
                self.next_nofm()
            self.wrotein = 1
        else:
            self.select_timeout()
        if platform != "win32":
            self.stdscr.move(3, 0)
            self.stdscr.clrtoeol()

    def writeinc_help(self):
        self.wconf()

    def confirm_left(self):
        """Go to previous contest"""
        self.contest = (self.contest - 1) % 13
        self.pcont(0, 1)
        self.state = STATE_CONTEST

    def confirm_right(self):
        """Go to next contest"""
        self.contest = (self.contest + 1) % 13
        self.pcont(0, 1)
        self.state = STATE_CONTEST

    def confirm_up(self):
        """Call it quits?"""
        self.done()
        self.play("Done2.wav", os.P_NOWAIT, 0, 0, 1, 1)
        self.state = STATE_CONFIRM

    def confirm_down(self):
        """We are done"""
        xml = open(self.xmlfile, "w")
        xml.write(ballotxml(self.date, self.country, self.State, self.county, self.ballot_number, self.precinct, self.serial, "voting_machine", self.sel, self.writeins))
        xml.close()
        p = PaperBallot(self.xmlfile)
        if self.printps:
            try:
                lp = os.popen(printcommand, "w")
                lp.write(p.GetPostScript())
                lp.close()
            except (IOError, EOFError), e:
                print e
        p.PostscriptPrint("ballot.ps")
        del p
        self.play("Printing.wav", os.P_WAIT, 0, 0, 0, 5)

    def confirm_help(self):
        self.play("Done2.wav", os.P_NOWAIT, 0, 0, 1, 1)

    def wconf(self):
        """Confirm write-in text"""
        if len(self.string) > 0:
            self.play("Conf1.wav", os.P_WAIT, 0, 0, 0, 1)
            self.visited[self.contest] = 1
            self.spellout(self.string)
        else:
            self.play("Void.wav", os.P_WAIT, 0, 0, 0, 1)
        self.play("Conf2.wav", os.P_NOWAIT, 0, 0, 0, 0)
        self.state = STATE_WRITEINC

    def next_nofm(self):
        """Get next candidate in an N of M contest"""
        self.ranked[self.cand] = 1
        self.rank += 1
        if self.rank <= self.length[self.contest]:
            self.play("Rank%.1d.wav" % self.rank, os.P_WAIT, 0, 1, 0, 2)
            self.cand = 0
            while self.cand < self.length[self.contest] and self.ranked[self.cand] == 1:
                self.cand += 1
            if self.cand < self.length[self.contest]:
                self.play("Cand%.2d%.1d.wav" % (self.contest, self.cand), os.P_WAIT, self.wait, 0, 0, 0)
            self.state = STATE_SELECT
        else:
            if self.confirm:
                self.play("Done2.wav", os.P_NOWAIT, 0, 0, 1, 1)
            else:
                self.play("Done1.wav", os.P_WAIT, 0, 0, 0, 2)
                self.done()
                self.play("Done3.wav", os.P_NOWAIT, 0, 0, 0, 0)
            self.confirm = 1
            self.state = STATE_CONFIRM

    def reset(self):
        curses.nocbreak()
        self.stdscr.keypad(0)
        curses.echo()
        curses.endwin()

    def main(self, country, State, county, precinct, date, machine_id, serial,
             session_ids, textmode, printps, debug, quick):
        self.country = country
        self.State = State
        self.county = county
        self.precinct = precinct
        self.date = date
        self.machine_id = machine_id
        self.serial = serial
        self.session_ids = session_ids
        self.textmode = textmode
        self.printps = printps
        self.debug = debug
        self.quick = quick
        self.ballot_number = str(machine_id) + "%.3d" % session_ids.pop()
        self.xmlfile = re.sub(' ', '_', "-".join(["v", str(date), country, State, county, str(precinct), str(self.ballot_number), str(serial)]) + ".xml")
        self.writeins = [["", ""], "", "", "", "", "", "", "", "", "", "", "", ""]
        self.sel = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, [], []]
        self.visited = [0] * 13
        self.state = STATE_INIT
        self.skill = 0
        self.cand = 0
        self.told = 0
        self.contest = 0
        self.confirm = 0
        try:
            if platform != "win32":
                self.stdscr = curses.initscr()
                if self.stdscr.getmaxyx()[0] < 24 or self.stdscr.getmaxyx()[1] < 80:
                    self.reset()
                    print "The terminal window size must be at least 24x80"
                    return 0
                curses.noecho()
                curses.cbreak()
                self.stdscr.keypad(1)
                self.stdscr.erase()
                self.addstr("*** Reading Impaired Interface ***", 1, 9)
            self.play("Start.wav", os.P_NOWAIT, 10, 0, 0, 0)
            self.rii()
            time.sleep(10)
        except KeyboardInterrupt:
            self.stopaudio()
            try:
                time.sleep(1)
            except KeyboardInterrupt:
                if platform != "win32": self.reset()
                return 0
        return 1

    def rii(self):
        while True:
# Wait until either a key is pressed, or the delay time expires.
            if self.mode == os.P_NOWAIT or self.delay > 0:
                now = time.time()
                while time.time() < now + self.delay:
                    if self.key_pressed(): break
                    time.sleep(.5)
                    if self.running(): now = time.time()
# Get next character typed on the keyboard, or -1 if nothing is typed.
            if self.delay > 0 or self.mode == os.P_NOWAIT:
                c = -1
                if self.key_pressed():
                    if self.pid > 0:
                        self.stopaudio()
                    c = self.getch()
            else:
                c = self.getch()
            self.c = c
            if self.debug and c!= -1:
                self.addstr(str(self.sel) + "\n" + str(self.writeins), 0, 0)
                if platform != "win32": self.stdscr.refresh()
            if self.state == STATE_INIT:
                if c == KEY_DOWN:
                    self.init_down()
                elif c == KEY_HELP:
                    self.init_help()
                elif c == -1:
                    self.play("Start.wav", os.P_NOWAIT, 10, 0, 0, 0)
                else:
                    self.beep()
            elif self.state == STATE_FOLDER:
                if c == KEY_DOWN:
                    self.folder_down()
                elif c == KEY_HELP:
                    self.folder_help()
                elif c != -1:
                    self.beep()
            elif self.state == STATE_INTRO:
                if c == KEY_DOWN:
                    self.intro_down()
                elif c == KEY_HELP:
                    self.intro_help()
                elif c != -1:
                    self.beep()
            elif self.state == STATE_CONTEST:
                if c == KEY_LEFT:
                    self.contest_left()
                elif c == KEY_RIGHT:
                    self.contest_right()
                elif c == KEY_UP:
                    self.contest_up()
                elif c == KEY_DOWN:
                    self.contest_down()
                elif c == KEY_HELP:
                    self.contest_help()
                elif c == -1:
                    time.sleep(1)
                else:
                    self.beep()
            elif self.state == STATE_SELECT:
                if c == KEY_LEFT:
                    self.select_left()
                elif c == KEY_RIGHT:
                    self.select_right()
                elif c == KEY_UP:
                    self.select_up()
                elif c == KEY_DOWN:
                    self.select_down()
                elif c == KEY_HELP:
                    self.select_help()
                elif c == -1:
                    self.select_timeout()
                else:
                    self.beep()
            elif self.state == STATE_WRITEINQ:
                if c == KEY_RIGHT:
                    self.writeinq_right()
                elif c == KEY_DOWN:
                    self.writeinq_down()
                elif c == KEY_HELP:
                    self.writeinq_help()
                elif c == -1:
                    time.sleep(1)
                else:
                    self.beep()
            elif self.state == STATE_WRITEIN1:
                if c == KEY_LEFT:
                    self.writein1_left()
                elif c == KEY_RIGHT:
                    self.writein1_right()
                elif c == KEY_UP:
                    self.writein1_up()
                elif c == KEY_DOWN:
                    self.writein1_down()
                elif c == 43:
                    self.writein1_plus()
                elif c == KEY_HELP:
                    self.writein1_help()
                elif c == -1:
                    time.sleep(1)
                else:
                    self.beep()
            elif self.state == STATE_WRITEIN2:
                if c == KEY_DOWN:
                    self.writein2_down()
                elif self.valid[c]:
                    self.writein2_type()
                elif c == KEY_HELP:
                    self.writein2_help()
                elif c == -1:
                    time.sleep(1)
                else:
                    self.beep()
            elif self.state == STATE_WRITEINC:
                if c == KEY_LEFT:
                    self.writeinc_left()
                elif c == KEY_DOWN:
                    self.writeinc_down()
                elif c == KEY_HELP:
                    self.writeinc_help()
                elif c == -1:
                    time.sleep(1)
                else:
                    self.beep()
            elif self.state == STATE_CONFIRM:
                if c == KEY_LEFT:
                    self.confirm_left()
                elif c == KEY_RIGHT:
                    self.confirm_right()
                elif c == KEY_UP:
                    self.confirm_up()
                elif c == KEY_DOWN:
                    self.confirm_down()
                    return
                elif c == KEY_HELP:
                    self.confirm_help()
                elif c == -1:
                    time.sleep(1)
                else:
                    self.beep()
            else:
                d("*** " + state)
