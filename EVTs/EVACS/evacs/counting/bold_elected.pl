#! /usr/bin/perl -w
#
#
 
$infile = shift @ARGV;
$outfile = scalar @ARGV?shift @ARGV:"${infile}.bold";
$marker = "() show grestore";
$marker_found = 0;

open FHI, "$infile" or die "$infile: $!";
open FHO, ">$outfile" or die "$outfile: $!";

while (<FHI>) {
  if ($marker_found) { 
    if  (m/elected/) {
      # found a string to transform
      print FHO bold_electeds($_);
    } else {
      #echo line
      print FHO;
      next;
    }
  } else {
    #echo line
    print FHO;
    if (m/$marker/) { $marker_found = 1; next; }
  }
  # transform this line
}

close FHI;
close FHO;


sub bold_electeds {
  my $inline = shift;
  my $outline="";
  my @strings = split /\.  /, $inline;
  foreach $string (@strings) {
    #remove  braces and show keyword
    $string =~ s/[()]//g;
    $string =~ s/show//g;
    if ($string =~ m/grestore/) {
      if  ($string =~ m/elected \d/) {
	 # bold this
      $string =~ s/^\s*(([\w.'-,-]+ )+elected \d)\./\/Helvetica-Bold findfont 10 scalefont setfont \($1.  \) show /;
      $outline = "$outline$string";
      } else {
	$outline="$outline$string";
      }
      last;
    }
    if ($string !~ m/elected \d/) {
      # regular string
      $outline = "$outline ($string.  ) show ";
    } else {
      # bold this
      $string =~ s/^\s*(([\w.'-,-]+ )+elected \d)/\/Helvetica-Bold findfont 10 scalefont setfont \($1.  \) show /;
      $outline = "$outline$string";
    }
  }
return $outline;
}


