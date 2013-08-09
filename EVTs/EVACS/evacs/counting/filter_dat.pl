#! /usr/bin/perl -w

# This file is (C) copyright 2001-2004 Software Improvements, Pty Ltd
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

use strict;

my $table1_in = shift @ARGV;
my $table1_out = shift @ARGV;
my $table2_in = shift @ARGV;
my $table2_out = shift @ARGV;

open INFILE, "$table1_in" or die "Couldn't open $table1_in for reading: $!";
open OUTFILE, ">$table1_out" or die "Couldn't open $table1_out for writing: $!";
{
my @names;
my @transfer_values;
my @exhausted;
my @ballots;
my @totals;
my @previous;
my @transferred;
# SIPL 2011-06-16 Added support for next available candidate
my @distribution;

#parse the input file;
while (<INFILE>) {
    my @line=split /:/, $_;

    if ($line[0] eq "CN") {
	#Candidate Name
	chomp $line[3];
	$names[$line[1]]=$line[2].", ".$line[3];

    } elsif ($line[0] eq "TV") {
	#Transfer Value
	chomp $line[2];
	$transfer_values[$line[1]]=$line[2];

    } elsif ($line[0] eq "EX") {
	#Papers Exhausted
	chomp $line[2];
	$exhausted[$line[1]]=$line[2];

    } elsif ($line[0] eq "BT") {
	#Ballots Transferred
	chomp $line[3];
	$ballots[$line[1]][$line[2]]=$line[3];

    } elsif ($line[0] eq "TT") {
	#Total Ballots
	chomp $line[2];
	$totals[$line[1]]=$line[2];

    } elsif ($line[0] eq "PS") {
	#Previous Count
	chomp $line[2];
	$previous[$line[1]]=$line[2];

    } elsif ($line[0] eq "VT") {
	#Votes Transferred to table 2
	chomp $line[2];
	$transferred[$line[1]]=$line[2];

    } elsif ($line[0] eq "DS") {
        # SIPL 2011-06-16 Added support for next available candidate
	#Distribution
	chomp $line[2];
	$distribution[$line[1]]=$line[2];

    } else {
	#Unknown
    }
}

close INFILE;

#construct the heading line
my $heading;
$heading="Count\tDescription of Choices Counted\t";
my $candidate;
foreach $candidate (@names) {
    $heading=$heading.$candidate."\t";
}
$heading=$heading."Papers Exhausted at Count\tTotal Papers Counted\tTransfer Value\tVotes transferred to Table II\t\n";

print OUTFILE $heading;
my $i=1;
#construct the other lines
foreach (@totals) {
    my $line;

    last unless $totals[$i];

    #count number
    $line=$i."\t";

    #previous count
    if ($previous[$i]) {
	$line=$line."On Papers at Count ".$previous[$i];
    }
    $line=$line."\t";

    #ballots
    my $j;
    for $j (0..$#names) {
	if ($ballots[$i][$j]) {
	    $line=$line.$ballots[$i][$j];
	}
	$line=$line."\t"
    }

    #papers exhausted
    if ($exhausted[$i]) {
	$line=$line.$exhausted[$i];
    }
    $line=$line."\t";

    #total papers at count
    if ($totals[$i]) {
	$line=$line.$totals[$i];
    }
    $line=$line."\t";

    #transfer value
    if ($transfer_values[$i]) {
	$line=$line.$transfer_values[$i];
    }
    $line=$line."\t";

    #votes transferred to table 2
    if ($transferred[$i]) {
	$line=$line.$transferred[$i];
    }
    $line=$line."\t";

    # SIPL 2011-06-16 Added support for next available candidate
    # print OUTFILE $line."\n\n";
    print OUTFILE $line."\n";
    if ($distribution[$i]) {
        print OUTFILE "\tNAC after ".$distribution[$i];
    }
    print OUTFILE "\n";
    $i++;
}

close OUTFILE;
}

{
open INFILE, "$table2_in" or die "Couldn't open $table2_in for reading: $!";
open OUTFILE, ">$table2_out" or die "Couldn't open $table2_out for writing: $!";
my @names;
my @exhausted;
my @votes;
my @lost_gained;
my @totals;
my @distribution;
my @fully_excluded;
my @partially_excluded;
my @elected;
# SIPL 2011-06-16 Added support for MJ (majority) data.
my @majority;

# SIPL 2011-06-16 DS lines were in the format:
#   DS:Candidate NAME
# but are now in the format
#   DS:2:Candidate NAME
# i.e., with the line number.
# $distribution[0]="";
# The same goes for MJ lines.

#parse the input file;
while (<INFILE>) {
    my @line=split /:/, $_;

    if ($line[0] eq "CN") {
	#Candidate Name
	chomp $line[3];
	$names[$line[1]]=$line[2].", ".$line[3];

    } elsif ($line[0] eq "EX") {
	#Papers Exhausted
	chomp $line[3];
	$exhausted[$line[1]][0]=$line[2];
	$exhausted[$line[1]][1]=$line[3];

    } elsif ($line[0] eq "VT") {
	#Votes Transferred
	chomp $line[4];
	$votes[$line[1]][$line[2]][0]=$line[3];
	$votes[$line[1]][$line[2]][1]=$line[4];

    } elsif ($line[0] eq "LG") {
	#Lost or Gained
	chomp $line[3];
	$lost_gained[$line[1]][0]=$line[2];
	$lost_gained[$line[1]][1]=$line[3];

    } elsif ($line[0] eq "TT") {
	#Total Votes
	chomp $line[2];
	$totals[$line[1]]=$line[2];

    } elsif ($line[0] eq "DS") {
	#Distribution
        # SIPL 2011-06-16 See notes on changed format above.
	# chomp $line[1];
	# push (@distribution, $line[1]);
	chomp $line[2];
	$distribution[$line[1]]=$line[2];

    } elsif ($line[0] eq "FE") {
	#Fully Excluded
	chomp $line[2];
	$fully_excluded[$line[1]]=$line[2];

    } elsif ($line[0] eq "PE") {
	#Partially Excluded
	chomp $line[2];
	$partially_excluded[$line[1]]=$line[2];

    } elsif ($line[0] eq "EL") {
	#Previous Count
	chomp $line[3];
	# SIPL 2011-06-09 Note ".=" operator; there
	#   may be more than one candidate elected in the same count.
	#   Added a period and space at the end to make it prettier.
	$elected[$line[1]].=$line[2]." elected ".$line[3].". ";

    } elsif ($line[0] eq "MJ") {
        # SIPL 2011-06-16 Added this clause.
	#Majority
	chomp $line[2];
	$majority[$line[1]]=$line[2];

    } else {
	#Unknown
    }
}

close INFILE;

#construct the heading line
my $heading;
$heading="Count\t";
my $candidate;
foreach $candidate (@names) {
    $heading=$heading.$candidate."\t";
}
$heading=$heading."Votes Exhausted at Count\tLoss by fraction\tTotal votes at End of the Count\tRemarks\t\n";

print OUTFILE $heading;
my $i=1;
#construct the other lines
foreach (@totals) {
    my $line1;
    my $line2;

    last unless $totals[$i];

    #count number
    $line1=$i."\t";
    $line2="\t";

    #ballots
    my $j;
    for $j (0..$#names) {
	if ($votes[$i][$j][0]) {
	    $line1=$line1.$votes[$i][$j][0];
	}
	if ($votes[$i][$j][1]) {
	    $line2=$line2.$votes[$i][$j][1];
	}
	$line1=$line1."\t";
	$line2=$line2."\t";
    }

    #votes exhausted
    if ($exhausted[$i][0]) {
	$line1=$line1.$exhausted[$i][0];
    }
    $line1=$line1."\t";
    if ($exhausted[$i][1]) {
	$line2=$line2.$exhausted[$i][1];
    }
    $line2=$line2."\t";

    #loss by fraction
    if ($lost_gained[$i][0]) {
	$line1=$line1.$lost_gained[$i][0];
    }
    $line1=$line1."\t";
    if ($lost_gained[$i][1]) {
	$line2=$line2.$lost_gained[$i][1];
    }
    $line2=$line2."\t";

    #total papers at count
    $line1=$line1."\t";
    if ($totals[$i]) {
	$line2=$line2.$totals[$i];
    }
    $line2=$line2."\t";

    #remarks
    # SIPL 2011-06-09 See note on changed format of DS lines above.
    # unless ($distribution[0] eq "") {
    if ($distribution[$i]) {
	# SIPL 2011-06-09 Added a space at the end to make it prettier.
	$line1=$line1.$distribution[$i]."'s votes distributed. ";
    }
    # shift @distribution;
    $line1=$line1."\t";
    if ($fully_excluded[$i]) {
	$line2=$line2.$fully_excluded[$i]." fully excluded. "
    }
    if ($partially_excluded[$i]) {
	# SIPL 2011-06-09 Added a space at the end to make it prettier.
	$line2=$line2.$partially_excluded[$i]." partially excluded. "
    }

    # SIPL 2011-06-16 Added support for MJ (majority) data.
    if ($majority[$i]) {
	$line2=$line2."Majority ".$majority[$i].". ";
    }

    if ($elected[$i]) {
	$line2=$line2.$elected[$i]
    }
    $line2=$line2."\t";

    print OUTFILE $line1."\n";
    print OUTFILE $line2."\n";
    $i++;
}

close OUTFILE;
}
