"""Generate Paper Ballots from XML

Author: Jan Karrman, Anand Pillai, David Mertz

Initial
----------------
Jan Karrman's PaperBallot function.

Date: Dec 15 2003
-----------------
Refactored by Anand Pillai to use python style string
templates.

Added background images (Jan)

Date: Mar 01 2004
-----------------
Moved the big post-script template chunk to a new file
in a compressed form (using zlib). We open this file
and decompress the data to get the post-script template
string. This reduces the size of this file considerably.

Date: April 7, 2004
-------------------
Added self-test code.  Use import line to read template.
Added xml2ps() wrapper.
"""
# -*- coding: iso-8859-1 -*-
import sys, os, time, re
from evm2003.utils.convert import votes2digits, obscure
from evm2003.utils.pdf417 import pdf417_codewords, pdf417_text
from evm2003.data.ballot import BALLOTPS
from gnosis.xml.objectify import make_instance

class PaperBallot:
    "The paper ballot class for EVM."
    def __init__(self, votefile="vote-selection.xml"):
        # the xml file containing the votes (ballot file)
        self.width = 8.5
        self.height = 11.0
        self.topmargin = 90.0
        self.leftmargin = 80.0
        self.rightmargin = 80.0
        self.belowheading = 50.0
        self.headsize = 18.0
        self.textsize = 13.0
        self.ballotnosize = 36.0
        self.ballotnovert = 54.0
        self.ballotnohoriz = 48.0
        self.bartype = 1
        self.barcodesize = 28.0
        self.barcodescale = 1.4
        self.barcodehoriz = 9.0
        self.lineheight1 = 1.0
        self.lineheight2 = 1.8
        self.arr1 = 11.0
        self.arrh = 4.0
        self.arrmin = 40.0
        self.votefile = votefile
        # Make ballot object by parsing the xml file.
        self.makeBallot()

    def makeBallot(self):
        "Creates the ballot object by parsing the vote file"
        # We are using David's gnosis.xml.objectify module here
        self.ballot = make_instance(self.votefile)

    def PostscriptPrint(self, filename="ballot.ps"):
        """ Print the ballot file to a postscript file.

        Parameters:
        (Explicit) filename: An output filename to write the PS.
        (Implicit) votefile: An XML file containing the casted votes.
        """
        try:
            psfile = open(filename, "w")
            psfile.write( self.GetPostScript() )
            psfile.close()
            return 0
        except (IOError, OSError, EOFError), e:
            print e
            return -1

    def GetPostScript(self):
        """ Return the Postscript data for the cast votes

        Author: Anand Pillai
        Date: 14 Nov 2003
        """
        heading = [ "OFFICIAL BALLOT",
                    "GENERAL ELECTION",
                    str(self.ballot.county) + ", " +
                    str(self.ballot.state) +
                    " Precinct " + str(self.ballot.precinct),
                    str(self.ballot.election_date) ]
        ballotno = self.ballot.number
        digits =  votes2digits(self.votefile)
        barcodenum = digits[:4] + obscure(digits[:4], digits[4:])

        keys = []
        values = []
        writeins = []
        for contest in self.ballot.contest:
            key = []
            if contest.coupled == "No":
                key.append(str(contest.name))
            n = 1
            value = []
            for selection in contest.selection:
                text = selection.PCDATA
                if selection.writein == "Yes":
                    writeins += [text]
                if contest.coupled == "Yes":
                    key.append(str(selection.name))
                if contest.ordered == "Yes" and text != "No preference indicated":
                    text = str(n) + " - " + str(text)
                    n += 1
                value.append(str(text))
            keys.append(key)
            values.append(value)

        # Break long lines; chars1 and chars2 are max number of characters in left
        # and right column respectively.
        chars1 = int((72*self.width/2 - self.leftmargin - self.arrmin)/(.6*self.textsize))
        chars2 = int((72*self.width/2 - self.rightmargin)/(.6*self.textsize))

        for i in range(len(keys)):
            L = []
            for j in range(len(keys[i])):
                l = keys[i][j].split(" ")
                p = l[0]
                for n in range(len(l)-1):
                    if len(p) + len(l[n+1]) + 1 <= chars1:
                        p += " " + l[n+1]
                    else:
                        L.append(p)
                        p = l[n+1]
                L.append(p)
            keys[i] = L

        length = []

        for i in range(len(values)):
            length.append(str(len(values[i])))
            L = []
            for j in range(len(values[i])):
                l = values[i][j].split(" ")
                p = l[0]
                for n in range(len(l)-1):
                    if len(p) + len(l[n+1]) + 1 <= chars2:
                        p += " " + l[n+1]
                    else:
                        while len(p) > chars2:
                            L.append(p[0:chars2])
                            p = p[chars2:]
                        L.append(p)
                        p = l[n+1]
                while len(p) > chars2:
                    L.append(p[0:chars2])
                    p = p[chars2:]
                L.append(p)
            values[i] = L

        barcode = os.getenv('BARCODE', 'Code128')
        if not re.match(r'(Code128|PDF417)$', barcode, re.I):
            print "Unknown barcode " + barcode + " using Code128"
            barcode = 'Code128'
        if re.match(r'Code128', barcode, re.I):
            # Calculate the checksum for the bar code. Insert start, stop and
            # checksum characters
            data = chr(137)
            checksum = 105
            for i in range(len(barcodenum)/2):
                n = int(barcodenum[2*i:2*i+2])
                data += chr(n+32)
                checksum += n*(i+1)
            data += chr(checksum % 103 + 32) + chr(138)
            # We need to quote some characters with a backslash in postscript strings
            data = re.sub(r'([\(\)\\])', r'\\\1', data)
            for i in range(len(heading)):
                heading[i] = re.sub(r'([\(\)\\])', r'\\\1', heading[i])

            for list in keys, values:
                for i in range(len(list)):
                    for j in range(len(list[i])):
                        list[i][j] = re.sub(r'([\(\)\\])', r'\\\1', list[i][j])
        else:
            self.bartype = 2
            self.barcodesize = 3
            codewords = pdf417_codewords(barcodenum +";" + ";".join(writeins))
            # The error correction level and number of rows and columns in the
            # barcode symbol should really be calculated from the number of
            # codewords, but these defaults should be okay for normal ballots
            # (rows=0 here means that the number of rows should be computed).
            # The barcode symbology requires 3 <= rows <= 90, 1 <= cols <= 30.
            # The ballot design requires rows*barcodesize < 35.
            errlevel = 4
            rows = 10
            cols = 0
            data = pdf417_text(codewords, rows, cols, errlevel)
        # Convert data to postscript data structures
        data += ") def\n/head [(" + ") (".join(heading) + ")] def\n/data [\n"
        for i in range(len(keys)):
            data += "["
            for j in range(len(keys[i])):
                data += "(" + keys[i][j] + ")"
            data += "()" * (max(len(keys[i]),len(values[i]))-len(keys[i])) + "]["
            for j in range(len(values[i])):
                data += "(" + values[i][j] + ")"
            data += "()" * (max(len(keys[i]),len(values[i]))-len(values[i])) + "]\n"
        # Calculate boundingbox
        llx = int(self.barcodehoriz)
        lly = int(self.ballotnovert - .71*self.ballotnosize)
        urx = int(72*self.width - self.barcodehoriz + .99)
        ury = int(72*self.height - self.ballotnovert + .71*self.ballotnosize + .99)
        bb = " ".join((str(llx), str(lly), str(urx), str(ury)))
        d = { "TIME" : str(time.asctime()),
              "BOUNDINGBOX" : bb,
              "WIDTH" : str(self.width),
              "HEIGHT" : str(self.height),
              "TOPMARGIN" : str(self.topmargin),
              "LEFTMARGIN" : str(self.leftmargin),
              "BELOWHEADING" : str(self.belowheading),
              "HEADSIZE" : str(self.headsize),
              "TEXTSIZE" : str(self.textsize),
              "BALLOTNOSIZE": str(self.ballotnosize),
              "BALLOTNOVERT" : str(self.ballotnovert),
              "BALLOTNOHORIZ" : str(self.ballotnohoriz),
              "BARCODETYPE" : str(self.bartype),
              "BARCODESIZE" : str(self.barcodesize),
              "BARCODESCALE" : str(self.barcodescale),
              "BARCODEHORIZ" : str(self.barcodehoriz),
              "LINEHEIGHT1" : str(self.lineheight1),
              "LINEHEIGHT2" : str(self.lineheight2),
              "ARR1" : str(self.arr1),
              "ARRH" : str(self.arrh),
              "BALLOTNO" : str(ballotno),
              "DATA" : data,
              "LENGTHTUPLE" : " ".join(length),
              "MARK" : "%%",
              "MARKEXCL" : "%!",
              "EXCL" : "%"
              }
        # Return the filled post script template
        return BALLOTPS % d

def xml2ps(xmlfile, psfile):
    PaperBallot(xmlfile).PostscriptPrint(psfile)

if __name__=='__main__':
    if len(sys.argv) != 3:
        print "USAGE:  python", sys.argv[0], "<ballot.xml> <ballot.ps>"
    else:
        xml2ps(*sys.argv[1:])
