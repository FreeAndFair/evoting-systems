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

$fn_rct = shift @ARGV;
$fn_vs = shift @ARGV;
$fn_results = shift @ARGV;
die "Usage: observer_check_verification_stmt.pl RECEIPT_FILE VERIFICATION_STMT_FILE" unless defined $fn_rct && $fn_vs && fn_results;

my $vss_tree = XML_Tree->new (snarf ($fn_vs));
my $rct_tree = XML_Tree->new (snarf ($fn_rct));

# Get the BSN from the receipt
my $bsn = $rct_tree->e ("BallotSequenceNumber")->characters ();

# Walk the verification statements looking for our BSN
my $nerrors = 0;
my $found = 0;
foreach my $vs_tree (grep {$_->name () eq "VoteVerificationStatement"} @{$vss_tree->elements ()}) {
   if ($bsn eq $vs_tree->e ("BallotSequenceNumber")->characters ()) {
      $found = 1;
      foreach my $vsc_tree (grep {$_->name () eq "VoteVerificationCode"} @{$vs_tree->elements ()}) {
         foreach my $rc_tree (grep {$_->name () eq "VoteVerificationCode"} @{$rct_tree->e ("VoteVerificationCodes")->elements ()}) {
            if ($vsc_tree->a ("QuestionReference") eq $rc_tree->a ("QuestionReference")) {
               if ($vsc_tree->characters () ne $rc_tree->characters ()) {
                  print "ERROR: mismatch on BSN #$bsn, " . "Question " . $rc_tree->a ("QuestionReference") . "\n";
                  $nerrors++;
               }
            }
         }
      }      
   }
}

if (!$found) {
   unsnarf ("<CheckResults>ERROR: can't find BSN #$bsn in verification statement</CheckResults>", $fn_results);
}
else {
   if ($nerrors > 0) {
      unsnarf ("<CheckResults>ERROR: $nerrors difference(s) between voter intent and vote receipt.</CheckResults>", $fn_results);
   }
   else {
      unsnarf ("<CheckResults>0:Success</CheckResults>", $fn_results);
   }
}