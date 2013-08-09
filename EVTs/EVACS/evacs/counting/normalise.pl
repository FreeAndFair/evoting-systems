#!/usr/bin/perl -w

# Takes a pagesize and a postscript file, and alters it to fit neatly
# in 1 page.

# (C) 2002-2004 Software Improvements Pty Ltd
# Based on posterize by Rusty Russell (c) 2001.  GPL.
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
use diagnostics;
use File::Basename;
use File::Copy;


# "constant" definitions
# 3% margins except for left margin which is 7% to accomodate punched holes
my $DEFAULT_MARGIN      = 0.03;
my $WIDE_MARGIN         = 0.07;
my $COUNT_FNAME         = "table1.ps";
my $DISTRIB_FNAME       = "table2.ps";
my $TRANSLATE_X         = 2000;
my $TRANSLATE_Y         = 5500;
my $TRANSLATE_COMMAND   = "$TRANSLATE_X $TRANSLATE_Y translate";
my $MULTIPAGE_MAX_SCALE = 0.5;  # At most two pages scaled into one

sub print_usage ($) {
	 print STDERR "@_\n";
	 print STDERR "Usage: " . basename($0) . " [--norotate] <papersize> <PS filename> ...\n";
	 print STDERR "\tMakes the file fit on the paper.\n";
}

#
# Script starts here
#
my $rotate;
my ($paper_width ,$paper_height);
my ($print_width, $print_height);
my ($left_margin, $adj_left_margin, $top_margin, $adj_top_margin, $left_offset, $top_offset);
my $file;
my @files;
my ($bbox, $bbox_x_min, $bbox_y_min, $bbox_x_max, $bbox_y_max);
my ($width, $height, $scale);
my $count_top_offset;
my $count_left_offset;
my $distrib_top_offset;
my $distrib_left_offset;
my @width_scale;
my @height_scale;
my @numpages;
my $file_temp;
my $file_idx;
my $marker;
my $pageno;


# Expecting a minimum of two arguments
if ($#ARGV < 1) {
	 print_usage("Not enough arguments.");
	 exit(1);
}

$rotate = 1;
if ($ARGV[0] eq "--norotate") {
	 shift;
	 $rotate = 0;
}

# Determine paper dimensions in Postscript units (equivalent to printer's point; 1/72 inch)
if ($ARGV[0] eq "letter") {
	 $paper_width  = 612;
	 $paper_height = 792;
}
elsif ($ARGV[0] eq "a4") {
	 $paper_width  = 595;
	 $paper_height = 842;
}
elsif ($ARGV[0] eq "a3") {
	 $paper_width  = 842;
	 $paper_height = 1190;
}
elsif ($ARGV[0] eq "a0") {
	 $paper_width  = 2384;
	 $paper_height = 3370;
}
elsif ($ARGV[0] eq "11x17") {
	 # ledger paper
	 $paper_width  = 792;
	 $paper_height = 1224;
}
elsif ($ARGV[0] eq "poster") {
	 $paper_width  = 3024;
	 $paper_height = 4000;
}
else {
	 print_usage("Unknown papersize $ARGV[0]. Change, or edit script");
	 exit(1);
}

# leave only the filenames on @ARGV
shift;

# Switch paper width and height
if ($rotate == 1) {
	 my $tmp = $paper_height;

	 $paper_height = $paper_width;
	 $paper_width = $tmp;
}

# Printable area and margins
$print_width  = $paper_width * (1.0000 - ($DEFAULT_MARGIN + $WIDE_MARGIN));
$print_height = $paper_height * (1.0000 - ($DEFAULT_MARGIN * 2));
$left_margin  = $paper_width * $WIDE_MARGIN;
$top_margin   = $paper_height * $DEFAULT_MARGIN;

$file = shift;
while(defined($file)) {
	 push @files, $file;

	 $bbox = `gs -sDEVICE=bbox  -dNOPAUSE -dBATCH $file 2>&1 >/dev/null | grep '^%%HiResBoundingBox' | cut -d: -f2`;
	 $_ = $bbox;
	 ($bbox_x_min, $bbox_y_min, $bbox_x_max, $bbox_y_max) = split;

	 if (!defined($bbox_x_min)) {
		  print STDERR "FATAL: Bounding box calculation failed for $file!\n";
		  exit(1);
	 }

	 $width  = $bbox_x_max - $bbox_x_min;
	 $height = $bbox_y_max - $bbox_y_min;

	 # Account for the fact that the generated Postscript tables
	 # do not have 0,0 as it's top left corner.
	 if (basename($file) eq $COUNT_FNAME) {
		  $count_top_offset  = $bbox_y_max - $TRANSLATE_Y;
		  $count_left_offset = $TRANSLATE_X - $bbox_x_min;
	 }
	 elsif (basename($file) eq $DISTRIB_FNAME) {
		  $distrib_top_offset  = $bbox_y_max - $TRANSLATE_Y;
		  $distrib_left_offset = $TRANSLATE_X - $bbox_x_min;
	 }

	 $scale = $print_width / $width;
	 if ($scale > 1.0000) {
		  push @width_scale, 1.0000;
	 }
	 else {
		  push @width_scale, $scale;
	 }

	 $scale = $print_height / $height;
	 if ($scale > 1.0000) {
		  push @height_scale, 1.0000;
		  push @numpages, 1;
	 }
	 elsif ($scale < $MULTIPAGE_MAX_SCALE) {
		  push @height_scale, $MULTIPAGE_MAX_SCALE;

		  if ((($height * $MULTIPAGE_MAX_SCALE) % $print_height) == 0) {
				push @numpages, (($height * $MULTIPAGE_MAX_SCALE) / $print_height);
		  }
		  else {
				push @numpages, (($height * $MULTIPAGE_MAX_SCALE) / $print_height) + 1;
		  }
	 }
	 else {
		  push @height_scale, $scale;
		  push @numpages, 1;
	 }

	 $file = shift;
}

$file_idx = 0;
foreach $file (@files) {
	 $file_temp   = "$file.tmp";

	 if (basename($file) eq $COUNT_FNAME) {
		  $top_offset  = $count_top_offset;
		  $left_offset = $count_left_offset;
		  $marker      = $TRANSLATE_COMMAND;
	 }
	 elsif (basename($file) eq $DISTRIB_FNAME) {
		  $top_offset  = $distrib_top_offset;
		  $left_offset = $distrib_left_offset;
		  $marker      = $TRANSLATE_COMMAND;
	 }
	 else {
		  $top_offset  = 0.0;
		  $left_offset = 0.0;
		  $marker      = "%%EndProlog";
	 }

	 $pageno = 1;
	 while ($pageno <= $numpages[$file_idx]) {
		  open(IFILE, "<$file") or die "Can't open file for reading \"$file\": $!\n";
		  open(OFILE, ">$file_temp") or die "Can't open temporary file \"$file_temp\": $!\n";

		  while (<IFILE>) {
				if (m/$marker/) {
					 last;
				}

				print OFILE $_;
		  }

		  if ($marker eq "%%EndProlog") {
				print OFILE $_;
		  }

#		  print OFILE "$left_margin $top_margin moveto 0 $paper_width rlineto $paper_height 0 rlineto 0 -$paper_width rlineto -$paper_height 0 rlineto\n" .
#				"gsave 0.5 setgray stroke grestore\n" .
#				"clip\n";

		  $adj_left_margin = $left_margin + ($left_offset * $width_scale[$file_idx]);

		  if ($rotate == 1) {
				if ($pageno > 1) {
					 $adj_top_margin = $top_margin + ($top_offset * $height_scale[$file_idx]) - (($pageno - 1) * $print_height);
				}
				else {
					 $adj_top_margin = $top_margin + ($top_offset * $height_scale[$file_idx]);
				}

				printf OFILE "%02.5f %02.5f translate\n", $adj_top_margin, $adj_left_margin;
				print OFILE "90 rotate\n";
		  }
		  else {
				if ($pageno > 1) {
					 $adj_top_margin = $top_margin + $print_height - ($top_offset * $height_scale[$file_idx]) + (($pageno - 1) * $print_height);
				}
				else {
					 $adj_top_margin = $top_margin + $print_height - ($top_offset * $height_scale[$file_idx]);
				}

				printf OFILE "%02.5f %02.5f translate\n", $adj_left_margin, $adj_top_margin;
		  }

		  printf OFILE "%02.5f %02.5f scale\n", $width_scale[$file_idx], $height_scale[$file_idx];

		  while (<IFILE>) {
				print OFILE $_;
		  }

		  print OFILE "\004\n";

		  close(IFILE);
		  close(OFILE);
		  rename $file_temp, "$file.$pageno";
		  ++$pageno;
	 }
		  ++$file_idx;
}


exit(0);
