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

# BUGBUG: running this without warnings (#!/usr/bin/perl -w) because getting the following warning:
#  "Use of uninitialized value in string eq at dre_gen_clear_text_ballot.pl line 57" for this line:
#
#     grep {$_->a ("AnswerReference") eq $aref} @{$_->elements ()}
#
#  If "AnswerReference" is changed to "QuestionReference", we don't see the warning

use files;
use XML_Tree;

$fn_results = shift @ARGV;
$fn_expected = shift @ARGV;
$fn_return = shift @ARGV;
die "Usage: audit_check_results.pl RESULTS_FILE RESULTS_EXPECTED_FILE " unless defined $fn_results && $fn_expected && $fn_return;

my $results_tree = XML_Tree->new (snarf ($fn_results));
my $expected_tree = XML_Tree->new (snarf ($fn_expected));

my $nerrors = 0;
my $questions;
foreach my $q_tree (grep {$_->name () eq "Question"} @{$results_tree->elements ()}) {
   my $qref = $q_tree->attribute ("QuestionReference");
   my $qtext = $q_tree->e ("Text")->characters ();
   foreach my $a_tree (grep {$_->name () eq "Answer"} @{$q_tree->elements ()}) {

      my $aref = $a_tree->attribute ("AnswerReference");
      my $atext = $a_tree->e ("Text")->characters ();
      my $votes = $a_tree->e ("Votes")->characters ();

      foreach (grep {$_->a ("QuestionReference") eq $qref} @{$expected_tree->elements ()}) {
         foreach $_ (grep {$_->a ("AnswerReference") eq $aref} @{$_->elements ()}) {
            my $votes_e = $_->e ("Votes")->characters ();
            if ($votes != $votes_e) {
               $nerrors++;
               print "ERROR: expected results do not match actual results!\n";
               print "   $qtext: $atext has $votes and should have $votes_e\n";
            }
         }
      }
   }
}

if ($nerrors == 0) {
   $error = "<CheckResults>0:Success</CheckResults>";
}
else {
   $error = "<CheckResults>ERROR: $nerrors difference(s) between expected and actual results.</CheckResults>";
}
unsnarf ($error, $fn_return);
