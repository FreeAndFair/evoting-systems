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

$fn_bb = shift @ARGV;
$fn_ctb = shift @ARGV;
$fn_re = shift @ARGV;
die "Usage: dre_gen_clear_text_ballot.pl BLANK_BALLOT_FILE CLEAR_TEXT_BALLOT_FILE RESULTS_EXPECTED_FILE " unless defined $fn_bb && $fn_ctb;

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

# Initialize the results_expected tree
my $re_tree;
eval {
   $re_tree = XML_Tree->new (snarf ("$fn_re"));
};
if ($@) {
   $re_tree = XML_Tree->construct ("Results");
   foreach (sort keys %$questions) {
      my $q = $_;
      my $ques = $re_tree->new_element ("Question");
      $ques->add_attribute ("QuestionReference", "$q");

      my $text = $ques->new_element ("Text");
      $text->add_characters ("$questions->{$q}->{title}");

      my $totalcast = $ques->new_element ("TotalVotesCast");
      $totalcast->add_characters ("0");

      foreach (sort keys %{$questions->{$q}->{answers}}) {
         my $ans = $ques->new_element ("Answer");
         $ans->add_attribute ("AnswerReference", "$_");

         my $text = $ans->new_element ("Text");
         $text->add_characters ("$questions->{$q}->{answers}->{$_}->{text}");

         my $votes = $ans->new_element ("Votes");
         $votes->add_characters ("0");
      }
   }
}

my $ctb_tree = XML_Tree->new (snarf ($fn_ctb));

# Update the results_expected
foreach my $a (grep {$_->name () eq "AnswerReference"} @{$ctb_tree->elements ()}) {
   # Add selection to results_expected
   foreach my $re_q (grep {$_->name () eq "Question"} @{$re_tree->elements ()}) {
      foreach my $re_a (grep {$_->a ("AnswerReference") eq $a->characters ()} @{$re_q->elements ()}) {
         my $votes = $re_a->e("Votes")->characters () + 1;
         $re_a->e("Votes")->remove_all_characters ();
         $re_a->e("Votes")->add_characters($votes);

         my $totalcast = $re_q->e("TotalVotesCast")->characters () + 1;
         $re_q->e("TotalVotesCast")->remove_all_characters ();
         $re_q->e("TotalVotesCast")->add_characters($totalcast);
      }
   }
}

unsnarf ($re_tree->internal_format_as_text () . "\n", "$fn_re");
