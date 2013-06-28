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
#     grep {$_->a ("AnswerReference") eq $a} @{$re_q->elements ()}
#
#  If "AnswerReference" is changed to "QuestionReference", we don't see the warning

use files;
use XML_Tree;

srand;   # not needed for 5.004 and later

$fn_bb = shift @ARGV;
$fn_ctb = shift @ARGV;
die "Usage: dre_gen_clear_text_ballot.pl BLANK_BALLOT_FILE CLEAR_TEXT_BALLOT_FILE " unless defined $fn_bb && $fn_ctb;

# Read the blank ballot
my $bb_tree = XML_Tree->new (snarf ($fn_bb));
my $questions;
foreach my $q_tree (grep {$_->name () eq "BallotQuestion"} @{$bb_tree->elements ()}) {
   my $qref = $q_tree->attribute ("QuestionReference");
   $questions->{$qref}->{title} = $q_tree->e ("QuestionTextStructure")->characters ();
   foreach my $answer_tree (grep {$_->name () eq "BallotAnswer"} @{$q_tree->elements ()}) {
      $questions->{$qref}->{answers}->{$answer_tree->attribute ("AnswerReference")}->{text} = $answer_tree->e ("AnswerTextStructure")->characters ();
  }
}

# Make the clear text ballot
my $clear_text_ballot_tree = XML_Tree->construct ("ClearTextBallot");
foreach (sort keys %$questions) {
   # Assume pick exactly one answer per question at random.  
   my $q = $_;
   my @answers = sort keys %{$questions->{$q}->{answers}};
   my $a = @answers[int(rand($#answers + 1))];

   # Add the selected answer to the voted ballot
   my $answer_ref_tree = $clear_text_ballot_tree->new_element ("AnswerReference");
   $answer_ref_tree->add_characters ($a);
}

unsnarf ($clear_text_ballot_tree->internal_format_as_text () . "\n", "$fn_ctb");
