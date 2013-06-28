#!/usr/bin/perl
# 
# This material is subject to the VoteHere Source Code Evaluation
# License Agreement ("Agreement").  Possession and/or use of this
# material indicates your acceptance of this Agreement in its entirety.
# Copies of the Agreement may be found at www.votehere.net.
# 
# Copyright 2004 VoteHere, Inc.  All Rights Reserved
# 
# You may not download this Software if you are located in any country
# (or are a national of a country) subject to a general U.S. or
# U.N. embargo or are deemed to be a terrorist country (i.e., Cuba,
# Iran, Iraq, Libya, North Korea, Sudan and Syria) by the United States
# (each a "Prohibited Country") or are otherwise denied export
# privileges from the United States or Canada ("Denied Person").
# Further, you may not transfer or re-export the Software to any such
# country or Denied Person without a license or authorization from the
# U.S. government.  By downloading the Software, you represent and
# warrant that you are not a Denied Person, are not located in or a
# national of a Prohibited Country, and will not export or re-export to
# any Prohibited Country or Denied Party.

use warnings;
use strict;
use FindBin;

my $dtd = qq($FindBin::Bin/vhti.dtd);
my $header = q(default-dtd.h);

if (! -r $dtd) {
  die "$dtd doesn't exist";
}

if ((! -r $header)
    ||
    -M($dtd) < -M ($header)) {

  open (DTD, '<', $dtd)
    or die "Can't open $dtd for reading: $!";

  open (HEADER, '>', $header)
    or die "Can't open $header for writing: $!";

  while (<DTD>) {
    chomp; s/\015+$//;
    s(("|\\))(\\$1)g;           # escape double-quotes and backslashes.
    print HEADER qq("$_\\n"\n);
  }

  close (HEADER);
  close (DTD);

  print "Regenerated $header.\n";

} else {
  print "$header is no older than $dtd; not regenerating.\n";
}
