#!/usr/bin/python

# Author: John-Paul Gignac

# Modified by Jan Karrman to generate XML with ballotxml() and connect with
# the printing routines.

# Import Modules
import os, pygame, re, sys, string, random
from pygame.locals import *
sys.path.append(os.path.join('..', '..'))
from evm2003.Print.PaperBallot import PaperBallot
from evm2003.utils.getxml import ballotxml
from evm2003.data.contests import *

country = "US"
state = "CA"
county = "Santa Clara County"
ballot_number = random.randint(1000, 1999)
precinct = 2216
date = 20081104
serial = 345
psfile = 'ballot.ps'

screen_width = 1280
screen_height = 1024

button_radius = 8

# Functions to create our resources
def load_image(name, colorkey=-1, size=None):
	fullname = os.path.join('graphics', name)
	try:
		image = pygame.image.load(fullname)
	except pygame.error, message:
		print 'Cannot load image:', fullname
		raise SystemExit, message

	if size is not None:
		image = pygame.transform.scale( image, size)
	image = image.convert()

	if colorkey is not None:
		if colorkey is -1:
			colorkey = image.get_at((0,0))
		image.set_colorkey(colorkey, RLEACCEL)
	return image

def xml_escape( str):
	str = string.replace( str, "&", "&amp;")
	str = string.replace( str, "<", "&lt;")
	str = string.replace( str, ">", "&gt;")
	str = string.replace( str, '"', "&quot;")
	str = string.replace( str, "'", "&apos;")
	return str

class Candidate:
	def __init__(self, contest, x, y, number, writein=0):
		self.contest = contest
		self.x = x
		self.y = y
		self.number = number
		self.writein = writein
		self.selected = 0

	def draw_button( self):
		if self.contest.ordered == 't':
			for i in range(self.contest.maxVotes):
				if self.selected == i+1:
					screen.blit(Ballot.small_selected,(self.x+13*i,self.y))
				else:
					screen.blit(Ballot.small_deselected,(self.x+13*i,self.y))

			text_rect = (self.x+120,self.y-3,12,16)
			screen.fill( (255,255,255), text_rect)
			if self.selected:
				textobj = Ballot.writein_font.render(
					`self.selected`+':', 0, (255, 0, 0))
				screen.blit( textobj, text_rect)

			pygame.display.update((self.x,self.y,13*self.contest.maxVotes,11))
			pygame.display.update(text_rect)

			text_rect = [self.x+135,self.y-3,130,16]
		else:
			if self.selected:
				screen.blit( Ballot.button_selected,
					(self.x-button_radius, self.y-button_radius))
			else:
				screen.blit( Ballot.button_deselected,
					(self.x-button_radius, self.y-button_radius))
			pygame.display.update(
				(self.x-button_radius,self.y-button_radius,
				button_radius*2,button_radius*2))

			text_rect = [self.x+button_radius+4,self.y-button_radius, 240, 16]

		if self.writein:
			if self.contest.coupled == 't':
				text_rect[0] += 8
				text_rect[2] -= 78
				text_rect[1] -= 18
				self.draw_writein(
					self.contest.ballot.writeins[self.contest.number][0],
					text_rect)
				text_rect[2] -= 18
				text_rect[1] += 22
				self.draw_writein(
					self.contest.ballot.writeins[self.contest.number][1],
					text_rect)
			else:
				self.draw_writein(
					self.contest.ballot.writeins[self.contest.number],
					text_rect)

	def draw_writein(self, text, text_rect):
		screen.fill( (255,255,255), text_rect)
		if self.selected:
			textobj = Ballot.writein_font.render( text, 0, (255, 0, 0))
			screen.blit( textobj, text_rect)
		pygame.display.update( text_rect)

	def reset(self):
		if self.selected:
			self.selected = 0
			self.draw_button()

	def toggle(self, value=1):
		if self.selected == value:
			self.selected = 0
			if self.contest.number < 11:
				ballot.votes[self.contest.number] = 0
			elif self.contest.number == 11:
				ballot.votes[11].remove(self.number)
			else:
				ballot.votes[12][value-1] = 0
		else:
			if self.contest.ordered == 't' or self.contest.maxVotes == 1:
				for candidate in self.contest.candidates:
					if candidate != self and candidate.selected == value:
						candidate.selected = 0
						candidate.draw_button()
			else:
				# Make sure there aren't too many selections
				count = 0
				for candidate in self.contest.candidates:
					if candidate.selected: count = count + 1
				if count >= self.contest.maxVotes: return

			self.selected = value
			if self.contest.number < 11:
				ballot.votes[self.contest.number] = self.number
			elif self.contest.number == 11:
				ballot.votes[11].append(self.number)
				ballot.votes[11].sort()
			else:
				ballot.votes[12][value-1] = self.number

			if self.writein:
				self.contest.edit_writein()

		self.draw_button()

class Contest:
	def __init__(self, ballot, number, minVotes, maxVotes, ordered, coupled):
		self.ballot = ballot
		self.number = number
		self.minVotes = minVotes
		self.maxVotes = maxVotes
		self.ordered = ordered
		self.coupled = coupled
		self.candidates = []

	def add_candidate(self, x, y, number):
		self.candidates.append( Candidate( self, x, y, number))

		# The following hack causes the last option to be treated
		# as a write-in whenever there are three or more options.
		if len(self.candidates) > 2:
			self.candidates[-2].writein = 0
			self.candidates[-1].writein = 1

	def reset(self):
		for candidate in self.candidates:
			candidate.reset()

	def click(self, x, y):
		if self.ordered == 't':
			for candidate in self.candidates:
				if (x >= candidate.x and
					x < candidate.x+270 and
					y >= candidate.y-5 and
					y < candidate.y+14):
					if candidate.selected == 0:
						# Make this candidate the next selection
						minsel = 0
						for cand in self.candidates:
							if cand.selected > minsel: minsel = cand.selected
						candidate.toggle( minsel + 1)
					elif candidate.writein:
						self.edit_writein()
		else:
			for candidate in self.candidates:
				if self.coupled == 't':
					# Allow a slightly taller active area
					if (x >= candidate.x-button_radius and
						x < candidate.x+button_radius+260 and
						y >= candidate.y-button_radius-20 and
						y < candidate.y+button_radius+20):
						candidate.toggle()
				else:
					if (x >= candidate.x-button_radius and
						x < candidate.x+button_radius+260 and
						y >= candidate.y-button_radius and
						y < candidate.y+button_radius):
						candidate.toggle()

	def draw(self):
		for candidate in self.candidates:
			if candidate.selected: candidate.draw_button()

	def edit_writein(self):
		contname = contnames[self.number]
		if self.coupled == 't':
			keyboard = OnScreenKeyboard(
				'Write-in Candidate for President',
				ballot.writeins[self.number][0])
			keyboard.edit()
			ballot.writeins[self.number][0] = keyboard.text
			keyboard = OnScreenKeyboard(
				'Write-in Candidate for Vice President',
				ballot.writeins[self.number][1])
			keyboard.edit()
			ballot.writeins[self.number][1] = keyboard.text
		else:
			keyboard = OnScreenKeyboard(
				'Write-in Candidate for '+contname,
				ballot.writeins[self.number])
			keyboard.edit()
			ballot.writeins[self.number] = keyboard.text
		self.ballot.draw()

class Ballot:
	def __init__(self):
		self.load()

	def load( self):
		self.votes = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, [], [0, 0, 0, 0, 0, 0, 0, 0]]
		self.writeins = [['', ''], '', '', '', '', '', '', '', '', '', '', '', '']

		self.contests = []

		headParser = re.compile("([0-9]+) ([0-9]+) ([tf]) ([tf])\n")
		parser = re.compile("([0-9]+) ([0-9]+)\n")

		try:
			f = open( "coords")
			contnum = 0
			while 1:
				line = f.readline()
				if line == '': break

				match = headParser.match(line)
				if match is None: break

				(minVotes,maxVotes,ordered,coupled) = match.groups()

				contest = Contest( self, contnum,
					int(minVotes), int(maxVotes), ordered, coupled)

				candnum = 1
				while 1:
					line = f.readline()
					if string.strip(line) == '': break

					match = parser.match(line)
					if match is not None:
						(x,y) = match.groups()
						contest.add_candidate( int(x), int(y), candnum)

					candnum += 1
				self.contests.append( contest)

				if line == '': break
				contnum += 1

			f.close()
		except: pass

	def draw( self):
		screen.blit( Ballot.image, (0,0))
		pygame.display.update()

		for contest in self.contests:
			contest.draw()

	def vote( self):
		self.draw()

		while 1:
			pygame.time.wait(20)
			for event in pygame.event.get():
				if event.type is KEYDOWN:
					if event.key == K_ESCAPE:
						return
				elif event.type is MOUSEBUTTONUP:
					pos = pygame.mouse.get_pos()

					for contest in self.contests:
						contest.click( pos[0], pos[1])

					if (pos[0] >= 1084 and pos[0] <= 1191 and
						pos[1] >= 643 and pos[1] <= 658):
						# Reset the grid
						self.contests[-1].reset()

					if (pos[0] >= 940 and pos[0] <= 1203 and
						pos[1] >= 860 and pos[1] <= 946):
						ballot.votes[12]
						for i in range(ballot.votes[12].count(0)):
							ballot.votes[12].remove(0)
						# Print the ballot
						xml = ballotxml(date, country, state, county, ballot_number, precinct, serial, 'voting_machine', ballot.votes, ballot.writeins)
						xmlfile = re.sub(' ', '_', "-".join(["v", str(date), country, state, county, str(precinct), str(ballot_number), str(serial)]) + ".xml")
						file = open(xmlfile, 'w')
						file.write(xml)
						file.close()
						p = PaperBallot(xmlfile)
						p.PostscriptPrint(psfile)
						del p

						return

class OnScreenKeyboard:
	def __init__( self, title, text=''):
		self.title = title
		self.text = text
		self.text_rect = None

	def draw( self):
		# Clear the screen
		screen.fill( (255, 255, 255))

		# Draw the title
		titleobj = self.titlefont.render( self.title, 1, (200,0,0))

		# Center it at the top of the screen
		titleleft = (screen_width - titleobj.get_width()) / 2
		screen.blit( titleobj, (titleleft, self.titletop))

		# Draw the keyboard
		screen.blit( self.image, (self.xpos, self.ypos))

		pygame.display.update()

		self.draw_text()

	def draw_text( self):
		if self.text_rect:
			# Clear the previous text
			screen.fill( (255, 255, 255), self.text_rect)

		# Render the text
		textobj = self.font.render( self.text, 0, (0,0,200))

		# Compute the x ccordintate for centering
		textleft = (screen_width-textobj.get_width()-self.cursor_width) / 2

		# Draw the text onto the screen
		screen.blit( textobj, (textleft, self.texttop))

		# Draw the cursor
		screen.fill( (0, 0, 0),
			(textleft+textobj.get_width(),self.texttop,
			self.cursor_width, textobj.get_height()))

		# Record the new text rectangle for later clearing
		new_text_rect = (textleft, self.texttop,
			textobj.get_width() + self.cursor_width, textobj.get_height())

		# Update the display
		pygame.display.update( new_text_rect)
		if self.text_rect:
			pygame.display.update( self.text_rect)

		# Record the new text rect for next time
		self.text_rect = new_text_rect

	def append_char( self, char):
		if len(self.text) < self.max_length:
			self.text = self.text + char
			self.draw_text()

	def backspace( self):
		self.text = self.text[:-1]
		self.draw_text()

	def edit( self):
		self.draw()

		while 1:
			pygame.time.wait(20)
			for event in pygame.event.get():
				if event.type is KEYDOWN:
					if event.key == K_ESCAPE:
						return
					elif event.key == K_SPACE:
						self.append_char(' ')
					elif event.key >= ord('a') and event.key <= ord('z'):
						self.append_char(chr(event.key-32))
					elif event.key == K_BACKSPACE:
						self.backspace()
					elif event.key == K_RETURN:
						return
				elif event.type is MOUSEBUTTONUP:
					pos = pygame.mouse.get_pos()

					# Make sure the mouse is within the bounds of the keyboard
					if( pos[0] >= self.xpos and pos[0] < self.xpos+768 and
						pos[1] >= self.ypos and pos[1] < self.ypos+360):
						# Determine the grid coordinates of the click
						gridx = (pos[0] - self.xpos) / 96
						gridy = (pos[1] - self.ypos) / 90

						# Determine the key being pressed
						if( gridy < 3 or gridx < 2):
							# It's an alphabetic char
							self.append_char( chr(65+gridx+gridy*8))
						elif( gridx < 4):
							# It's the SPACE key
							self.append_char( ' ')
						elif( gridx < 6):
							# It's the backspace key
							self.backspace()
						else:
							# It's the DONE key
							return

# Function to set the video mode
def set_video_mode():
	global screen

	screen = pygame.display.set_mode( (screen_width, screen_height),
		FULLSCREEN)
	pygame.display.set_caption('OVC Demo')

def setup_everything():
	# Initialize the game module
	pygame.init()

	set_video_mode()

	Ballot.image = load_image('ballot-mockup3.png', None,
		(screen_width, screen_height))

	Ballot.button_deselected = load_image('button-deselected.png',None,(16,16))
	Ballot.button_selected = load_image('button-selected.png',None,(16,16))
	Ballot.small_deselected = load_image('small-deselected.png',None,(11,11))
	Ballot.small_selected = load_image('small-selected.png',None,(11,11))

	OnScreenKeyboard.image = load_image('keyboard.png', None, (769, 361));
	OnScreenKeyboard.xpos = (screen_width - 769) / 2
	OnScreenKeyboard.ypos = (screen_height - 361) / 2 + 100
	OnScreenKeyboard.fontsize = 50
	OnScreenKeyboard.font = pygame.font.SysFont('arial',
		OnScreenKeyboard.fontsize)
	OnScreenKeyboard.texttop = 300
	OnScreenKeyboard.titlefontsize = 36
	OnScreenKeyboard.titlefont = pygame.font.SysFont('arial',
		OnScreenKeyboard.titlefontsize)
	OnScreenKeyboard.titletop = 150
	OnScreenKeyboard.cursor_width = 20
	OnScreenKeyboard.max_length = 24

	Ballot.writein_font = pygame.font.SysFont('arial', 12)

setup_everything()

def intro_screen():
	global screen

	continue_image = load_image('continue.png', None)
	screen.fill( (255,255,255))
	screen.blit( continue_image, (534,494))
	pygame.display.update()

	while 1:
		pygame.time.wait(20)
		for event in pygame.event.get():
			if event.type is MOUSEBUTTONDOWN:
				return 0

			if event.type is KEYDOWN:
				if event.key == K_ESCAPE: return 1
				return 0

if not intro_screen():
	ballot = Ballot()
	ballot.vote()
