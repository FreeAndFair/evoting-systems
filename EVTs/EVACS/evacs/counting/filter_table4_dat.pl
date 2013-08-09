#! /usr/bin/perl -w

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

use strict;

my $table4_in = shift @ARGV;
my $table4_out = shift @ARGV;

open INFILE, "$table4_in" or die "Couldn't open $table4_in for reading: $!";
open OUTFILE, ">$table4_out" or die "Couldn't open $table4_out for writing: $!";
{
my $electorate;
my @polling_places;
my @candidates;
my @ballots;
my @t1p;
my @ttfor;
my @ttinf;
my @tot;
my $totfor;
my $totinf;
my $tottot;

# SIPL 2011-09-26 If there are no votes, the input is missing
#   the three total lines.  So initialize the values to 0.
$totfor = '0';
$totinf = '0';
$tottot = '0';

#parse the input file;
while (<INFILE>) {
    chomp;
    my @line=split /:/, $_;

    if ($line[0] eq "EL") {
	#Electorate Name
	$electorate=$line[2];

    } elsif ($line[0] eq "PP") {
	#Polling place
	$polling_places[$line[1]]=$line[2];

    } elsif ($line[0] eq "CAN") {
	#Candidate/party data
	$candidates[$line[1]][$line[2]]=$line[3];

    } elsif ($line[0] eq "DT") {
	#Ballots from polling place
	$ballots[$line[1]][$line[2]]=$line[3];

    } elsif ($line[0] eq "T1P") {
	#Total first preferences for a candidate
	$t1p[$line[1]]=$line[2];

    } elsif ($line[0] eq "TTFOR") {
	#Formal votes
	$ttfor[$line[1]]=$line[2];

    } elsif ($line[0] eq "TTINF") {
	#Informal votes
	$ttinf[$line[1]]=$line[2];

    } elsif ($line[0] eq "TOT") {
	#Polling place total
	$tot[$line[1]]=$line[2];

    } elsif ($line[0] eq "TOTFOR") {
	#Formal votes in total column
	$totfor=$line[1];

    } elsif ($line[0] eq "TOTINF") {
	#Informal votes in total column
	$totinf=$line[1];

    } elsif ($line[0] eq "TOTTOT") {
	#Polling place total in total column
	$tottot=$line[1];

    } else {
	#Unknown
    }
}

close INFILE;

#construct the heading line
my $heading;
$heading="First preference votes by polling place:\t";
$heading .= $electorate;
$heading .= "\n\nCandidate\tParty/Group";
my $pp;
foreach $pp (@polling_places) {
    $heading=$heading."\t".$pp;
}
$heading=$heading."\tTotal\n\n";

print OUTFILE $heading;
my $i;
#construct lines for candidates
for $i (0..$#candidates) {
    my $line;

    #name
    $line=$candidates[$i][0];

    #party/group
    $line .= "\t".$candidates[$i][1];


    #ballots
    my $j;
    for $j (0..$#polling_places) {
	$line=$line."\t";
	if (defined $ballots[$i][$j]) {
	    $line=$line.$ballots[$i][$j];
	}
    }

    #total
    $line .= "\t".$t1p[$i];

    print OUTFILE $line."\n";
}
#construct lines for totals
print OUTFILE "\n";

{
    my $line;

    $line="Formal\t";

    #ballots
    my $j;
    for $j (0..$#polling_places) {
	$line=$line."\t";
	if (defined $ttfor[$j]) {
	    $line=$line.$ttfor[$j];
	}
    }

    #total
    $line .= "\t".$totfor;

    print OUTFILE $line."\n";
}

{
    my $line;

    $line="Informal\t";

    #ballots
    my $j;
    for $j (0..$#polling_places) {
	$line=$line."\t";
	if (defined $ttinf[$j]) {
	    $line=$line.$ttinf[$j];
	}
    }

    #total
    $line .= "\t".$totinf;

    print OUTFILE $line."\n";
}

{
    my $line;

    $line="Polling place total\t";

    #ballots
    my $j;
    for $j (0..$#polling_places) {
	$line=$line."\t";
	if (defined $tot[$j]) {
	    $line=$line.$tot[$j];
	}
    }

    #total
    $line .= "\t".$tottot;

    print OUTFILE $line."\n";
}

close OUTFILE;
}
