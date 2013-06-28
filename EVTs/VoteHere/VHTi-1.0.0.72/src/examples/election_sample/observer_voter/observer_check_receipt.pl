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

$fn_ctb = shift @ARGV;
$fn_cb = shift @ARGV;
$fn_rct = shift @ARGV;
$fn_results = shift @ARGV;
die "Usage: observer_check_receipt.pl BALLOT_FILE CODEBOOK_FILE RECEIPT_FILE " 
   unless defined $fn_ctb && $fn_cb && $fn_rct && fn_results;

my $ctb_tree = XML_Tree->new (snarf ($fn_ctb));
my $cb_tree = XML_Tree->new (snarf ($fn_cb));
my $rct_tree = XML_Tree->new (snarf ($fn_rct));

# Build code array from the codebook tree
my $cb;
foreach my $q_tree (grep {$_->name () eq "DictionaryQuestion"} @{$cb_tree->elements ()}) {
   foreach my $a_tree (grep {$_->name () eq "DictionaryVerificationCode"} @{$q_tree->elements ()}) {
      my $aref = $a_tree->a ("AnswerReference");
      $cb->{$aref}->{vc} = $a_tree->characters ();
  }
}
my @cb_codes = sort keys %$cb;

# Build the receipt codes array
my @rct_codes;
foreach my $a_tree (grep {$_->name () eq "VoteVerificationCode"} @{$rct_tree->e ("VoteVerificationCodes")->elements ()}) {
   push(@rct_codes, $a_tree->characters ());
}

# Look-up the codes for the ballot choices
my @ctb_codes;
foreach my $aref (grep {$_->name () eq "AnswerReference"} @{$ctb_tree->elements ()}) {
   foreach (grep {$_ eq $aref->characters ()} @{cb_codes}) {
      push(@ctb_codes, $cb->{$_}->{vc});
   }
}

# Compare
my $nerrors = 0;
if ($#rct_codes != $#ctb_codes) {
   die "ERROR: unequal number of verification codes in ballot and verification receipt.";
}
for (my $i = 0 ; $i<=$#ctb_codes ; $i++) {
   if ($ctb_codes[$i] ne $rct_codes[$i]) {
      $nerrors++;
   }
}

if ($nerrors > 0) {
   unsnarf ("<CheckResults>ERROR: $nerrors difference(s) between voter intent and vote receipt.</CheckResults>", $fn_results);
}
else {
   unsnarf ("<CheckResults>0:Success</CheckResults>", $fn_results);
}