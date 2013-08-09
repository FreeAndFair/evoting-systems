#! /bin/sh

# This file is (C) copyright 2001-2007 Software Improvements, Pty Ltd
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 2 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

# If printer is postscript, set this to 1
POSTSCRIPT=1

# printer type (as known to ghostscript)
PRINTER_DEVICE="lj4dith"
PAPERSIZE="a3"
OUTPUTDIR="/tmp"

# root directory (where the scripts are)
SCRIPTROOT=/opt/eVACS/bin

# command to convert ps into bitmap
GSCOMMAND="gs -q -sDEVICE=$PRINTER_DEVICE -r600x600 -sPAPERSIZE=$PAPERSIZE -dNOPAUSE -dSAFER -sOutputFile=$OUTPUTDIR/raw"

# post-process ps to BOLD 'so& so was elected n' statements in table2
$SCRIPTROOT/bold_elected.pl $OUTPUTDIR/table2.ps
mv  $OUTPUTDIR/table2.ps.bold  $OUTPUTDIR/table2.ps
rm -f  $OUTPUTDIR/table2.ps.bold

# Centre postscript output on a3/a4 page.
$SCRIPTROOT/normalise.pl $PAPERSIZE $OUTPUTDIR/table1.ps $OUTPUTDIR/table2.ps

if [ $POSTSCRIPT -eq 0 ]; then
    # FOR NON-POSTSCRIPT PRINTER
    for file in $OUTPUTDIR/table[1,2]*.ps; do
		  echo quit | $GSCOMMAND $file
		  echo printing
		  # lpr $OUTPUTDIR/raw
	 done

    # Tables 3 and 4 are on A4 sized paper

# NOTE:
#  While the code has been placed here to print the Table 3 and Table 4 files,
#   at this stage the files are not to be printed.

#    PAPERSIZE="a4"
#    GSCOMMAND="gs -q -sDEVICE=$PRINTER_DEVICE -r600x600 -sPAPERSIZE=$PAPERSIZE -dNOPAUSE -dSAFER -sOutputFile=$OUTPUTDIR/raw"
#    for file in $OUTPUTDIR/table[3,4]*.ps; do
#                  echo quit | $GSCOMMAND $file
#                  echo printing
#         done

else
	 # FOR POSTSCRIPT PRINTER
	 lpr $OUTPUTDIR/table1.ps.*
	 lpr $OUTPUTDIR/table2.ps.*
#	 lpr $OUTPUTDIR/table3.ps
#	 lpr $OUTPUTDIR/table4.*.ps
fi

# remove normalised pages ready for another scrutiny
rm -f $OUTPUTDIR/table*.ps*

exit 0	
