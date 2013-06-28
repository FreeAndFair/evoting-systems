#!/usr/bin/perl -w
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

use files;
use XML_Tree;

$fn_in = '';
$fn_bsn = '';
$fn_out = '';

$fn_in = shift @ARGV;
$fn_bsn = shift @ARGV;
$fn_out = shift @ARGV;
die "Usage: audit_get_codebook.pl IN_XML_FILE BSN_XML_FILE OUT_XML" unless defined $fn_in && $fn_bsn && $fn_out;

my $in_tree = XML_Tree->new (snarf ("$fn_in"));
my $bsn = XML_Tree->new (snarf ("$fn_bsn"))->characters ();

my $found = 0;
foreach my $tree (grep {$_->name () eq "VoteVerificationDictionary"} @{$in_tree->elements ()}) {
   if ($bsn eq $tree->e ("BallotSequenceNumber")->characters ()) {
      $found = 1;
      unsnarf ($tree->internal_format_as_text () . "\n", $fn_out);
      last;
   }
}
if (!$found) {
   die "ERROR: can't find BSN #$bsn in set of revealed codebooks\n";
}

