"""
Filename: evmui.py
Project : The Electronic Voting Machine 2003
Purpose : This file contains initial source code for a
          rudimentary electronic PC based voting machine

Description: A simple tkinter based GUI which allows you
             to select candidates and sumbit a vote.
             
Created : Matt Shomphe, Jul 2003

Review/Modification History
---------------------------

Reviewed by Anand Pillai Aug 07 2003
1. Added this history/file comment header
2. Added comments for functions which did not have them
3. Comment strings use \" and internal strings use \'
4. Renamed file to evmui.py
""" 


from Tkinter import *
from tkMessageBox import showinfo, askyesno, showerror
from random import random
from time import time

__version__ = '0.001'

COMMENTS = """
There should be a collection of objects:
1. A Voter (data about the particular voter)
2. A VoteObject (a collection of data about a particular vote)
3. A VoteFrame (the interface which a voter uses)

[Note: There should also be a web interface, but this might have to be different.
It should still generate a VoteObject.]

A VoteObject contains information about the Voter and the vote that was recorded
from the vote object.

Right now we just have the VoteFrame.


VoteFrame APIs:

(1) attributes
- candidates -> A list or tuple of candidate names
- actions -> This is the list of buttons and their associated actions. [['text of button', action]]
It may be better if this isn't exposed.

(2) methods
- build() -> creates the object
- run() -> starts the object
- onVote() -> Actions associated with 'Vote' button
- onQuit() -> quit behavior
- onPrint() -> print behavior (undef right now).
"""

class BallotObject:

    def __init__(self, voterid):
        self.voterid = voterid
        self.president = None
        self.id = int(time())

    def ballot(self):
        s = """
        <?xml version='1.0'?>
        <vote id='%s'>
        <voter id='%s'/>
        <ballot>
        <president>%s</president>
        </ballot>
        </vote>
        """ % (self.id, self.voterid, self.president)
        return(s.strip())
        
class Voter:
    pass

class VoteFrame(Frame):
    """ This is the basic voting UI object """
    
    def __init__(self, parent=None):
        Frame.__init__(self, parent)
        self.candidates = []
        self.actions = [['Vote', self.onVote],
                        ['Quit', self.onQuit],
                        ['Print', self.onPrint]]
        self.var =StringVar()
        self.other=None
        self.otherstr ='Other'
        self.voter = str(random())[2:] # generate a random ID
        self.ballot = BallotObject(self.voter)
        
    def build(self):
        """ Creates the Voting UI """
        
        Label(self, text='Vote For President!').pack()
        self.__buildCandidates()
        self.__buildActions()
        self.master.title('Voter v%s' %__version__)
        self.pack()
        return(self)
    
    def run(self):
        """ Runs program mainloop """
        
        self.mainloop()
        
    def __buildCandidates(self, event=None):
        """ Builds gui elements populating them
        with list of candidates """
        
        candidates = self.candidates
        if not candidates:
            raise ValueError, (1, 'Failed to provide the object with cadidates')
        
        for candidate in candidates:
            row = Frame(self)
            Radiobutton(row, text=candidate, variable=self.var, value=candidate).pack(side=LEFT,fill=X)
            row.pack(side=TOP, fill=BOTH)

        other = self.otherstr
        row = Frame(self)
        Radiobutton(row, text=other, variable=self.var, value=other).pack(side=LEFT)
        eRow = Entry(row)
        eRow.pack(side=RIGHT, fill=X, expand=YES)
        row.pack(fill=X, expand=YES)
        self.other=eRow
        
    def __buildActions(self):
        """ Creates buttons and associates them with user
        actions """
        
        actions = self.actions
        row = Frame(self)

        for action in actions:
            txt, act = action
            Button(row, text=txt, command=act).pack(side=LEFT)
            
        row.pack()
        return(None)
    
    def onVote(self, event=None):
        """
        Called when the 'Vote' button is pressed.  In theory,
        this should create a 'VoteObject' that can be printed or handled
        in some way. """
        
        v = self.var.get()
        if v == self.otherstr:
            v = self.other.get()
            self.other.delete(0,END)

        if not v:
            showerror('Error!', 'You need to pick someone to vote for!')
            return(None)
        
        showinfo('You voted for...', v)
        self.ballot.president=v
        return(None)
    
    def onQuit(self, event=None):
        """ Event handler for quitting the UI """
        
        if askyesno('Verify Quit', 'Really quit?'): Frame.quit(self)
        
    def onPrint(self, event=None):
        """ Prints to a file named 'ballot<timestamp>' """

        filename = 'ballot%s.xml'%int(time())
        open(filename, 'w').write(self.ballot.ballot())
        return (None)
        
if __name__ == "__main__":

    vf = VoteFrame()
    vf.candidates = ['Howard Dean',
                     'George W. Bush',
                     'John Kerry',
                     'Richard Gephardt',
                     'Bob Graham']
                     
    vf.build().run()

