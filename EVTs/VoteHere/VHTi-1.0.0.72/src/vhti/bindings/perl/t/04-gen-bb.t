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

# Here we ask generate_blank_ballot to generate more answer marks than
# there are elements in the subgroup.  Since this is impossible, we
# expect it to fail.

use Test::More tests => 12;

use warnings;
use strict;
use Data::Dumper;

use VHTI;
use VHTI::gen_blank_ballot;

use FindBin;
use lib ($FindBin::Bin,
         "$FindBin::Bin/../examples",
         "$FindBin::Bin/../../../../toast/modules");
use common;
use constants;
use files;
use XML_Tree;

my $subgroup_order = 23;
my $generator = 17;



# Normally we'd just snarf a CryptoElectionParameters from a file
# lying around, but in this case we want to use a really small
# subgroup order, so we construct it by hand.
my $cep_tree = XML_Tree->construct ("CryptoElectionParameters");
{
  my $cgp_tree = $cep_tree->new_element ("CryptoGroupParameters");
  my $em_tree = $cgp_tree->new_element ("ElectionModulus");
  $em_tree->add_attribute ("Encoding", "DEC");
  $em_tree->add_characters ("47");
  my $esm_tree = $cgp_tree->new_element ("ElectionSubgroupModulus");
  $esm_tree->add_attribute ("Encoding", "DEC");
  $esm_tree->add_characters ($subgroup_order);
  my $esg_tree = $cgp_tree->new_element ("ElectionSubgroupMember");
  $esg_tree->add_attribute ("Encoding", "DEC");
  $esg_tree->add_characters ($generator);
  my $ctp_tree = $cep_tree->new_element ("CryptoTabulationParameters");
  my $epk_tree = $ctp_tree->new_element ("ElectionPublicKey");
  $epk_tree->add_attribute ("Encoding", "DEC");
  $epk_tree->add_characters ("1"); # a perfectly good public key!
  $ctp_tree->new_element ("NumAuth")->add_characters ("1");
  $ctp_tree->new_element ("Threshold")->add_characters ("1");
  my $ksc_tree = $ctp_tree->new_element ("KeyShareCommitment");
  $ksc_tree->add_attribute ("AuthFingerprint", "0");
  $ksc_tree->add_attribute ("Encoding", "DEC");
  $ksc_tree->add_characters ("1");
}

sub go {
  my $excess_answers = shift;
  my $use_answer_skeleton = shift;
  my $expected_exception = shift;

  my $num_ans = ($subgroup_order + $excess_answers - 1);

  my $answer_skeleton = join (qq(\n),
                              map  {
                                qq(<AnswerSkeleton> <AnswerTextStructure> a$_ </AnswerTextStructure> </AnswerSkeleton>)
                              }
                              ( 1 .. $num_ans));

  my $question_skeleton;
  if ($use_answer_skeleton) {
    $question_skeleton = qq(<QuestionSkeleton>
                         <QuestionTextStructure>
                           q1
                         </QuestionTextStructure> $answer_skeleton </QuestionSkeleton>);
  } else {
    $question_skeleton = qq(<QuestionSkeleton NumAns="$num_ans"><QuestionTextStructure> q1 </QuestionTextStructure></QuestionSkeleton>);
  }
  my $ballot_skeleton = q(<BallotSkeleton>
                       <ElectionID>
                         Hunt the Duplicate Answer Marks for fun and profit
                       </ElectionID>
                       <PrecinctID>
                         87th
                       </PrecinctID>
                       )
    . $question_skeleton
      . q(</BallotSkeleton>);

  my $return_value;
  eval {
    $return_value =
      VHTI::gen_blank_ballot::generate_blank_ballot ($ballot_skeleton,
                                                     $cep_tree->format_as_text (),
                                                     ALPHABET_ENCODING);
  };
  like ($@, $expected_exception, "got expected exception, or lack thereof");

  $return_value;
}

my $bb_xml;

foreach (0, 1) {
  go (1, $_, qr(NUM_ANSWERS_NOT_LESS_THAN_SUBGROUP_ORDER));
  diag ("Patience!");
}

foreach (0, 1) {
  $bb_xml = go (0, $_, qr());
}


# Stolen from "The Perl Cookbook"
sub trim {
  my @out = @_;
  for (@out) {
    s/^\s+//;
    s/\s+$//;
  }
  return wantarray ? @out : $out[0];
}

# Now check that the answer marks are unique.
my $bee_bee_tree = XML_Tree->new ($bb_xml);

sub snarf_answer_marks {
  my $bee_bee_tree = shift;
  my $return_value;
  foreach my $q (grep { $_->name () eq "BallotQuestion"} @{$bee_bee_tree->elements ()}) {
    foreach my $a (grep {$_->name () eq "BallotAnswer"} @{$q->elements ()} ) {
      my $am = trim ($a->e ("AnswerMark")->characters ());
      $return_value->{$am}++;
    }
  }
  $return_value;
}

my $answer_marks_seen = snarf_answer_marks ($bee_bee_tree);

{
  my $dups_seen = 0;
  foreach my $am (sort keys %$answer_marks_seen) {
    if ($answer_marks_seen->{$am} != 1) {
      $dups_seen++;
      last;
    }
  }

  if ($dups_seen) {
    diag (Dumper ($answer_marks_seen));
    fail ("Duplicate answer marks");
  } else {
    pass ("No duplicate answer marks");
  }
}

# Here we're *expecting* it to generate duplicate answer marks, but
# that's OK as long as the duplicates are all in different questions.
{
  my $ballot_skeleton = q(<BallotSkeleton>
                       <ElectionID>
                         We *expect* duplicate answer marks!  They're cool!  Don't panic!
                       </ElectionID>
                       <PrecinctID>
                         87th
                       </PrecinctID>
                       )
    . qq(<QuestionSkeleton NumAns="@{[$subgroup_order - 1]}"><QuestionTextStructure>How come?</QuestionTextStructure></QuestionSkeleton>)
      . qq(<QuestionSkeleton NumAns="@{[$subgroup_order - 1]}"><QuestionTextStructure>What for?</QuestionTextStructure></QuestionSkeleton>)
        . q(</BallotSkeleton>);

  my $return_value =
    VHTI::gen_blank_ballot::generate_blank_ballot ($ballot_skeleton,
                                                   $cep_tree->format_as_text (),
                                                   ALPHABET_ENCODING);
  pass ("OK to have more answers than the subgroup order, as long as no individual question has too many");
}

# We're not allowed to specify both NumAns *and* answer skeletons,
# even if the value of NumAns is correct.  Check that the call indeed
# fails in that case.
{
  my $answer_skeleton = qq(<AnswerSkeleton> <AnswerTextStructure> a0 </AnswerTextStructure> </AnswerSkeleton>);
  my $question_skeleton= qq(<QuestionSkeleton NumAns="1">
                         <QuestionTextStructure>
                           q1
                         </QuestionTextStructure> $answer_skeleton </QuestionSkeleton>);
  my $ballot_skeleton = q(<BallotSkeleton>
                       <ElectionID>
                         Hunt the Duplicate Answer Marks for fun and profit
                       </ElectionID>
                       <PrecinctID>
                         87th
                       </PrecinctID>
                       )
    . $question_skeleton
      . q(</BallotSkeleton>);

  eval {
    VHTI::gen_blank_ballot::generate_blank_ballot ($ballot_skeleton,
                                                   $cep_tree->format_as_text (),
                                                   ALPHABET_ENCODING);

  };
  like ($@, qr(NUM_ANS_ATTRIBUTE_AND_ANSWER_SKELETON), "Got expected failure");
  # Ensure the code detects non-numbers where there oughta be numbers.

  $question_skeleton= qq(<QuestionSkeleton NumAns="oh no!!">
                         <QuestionTextStructure>
                           q1
                         </QuestionTextStructure> $answer_skeleton </QuestionSkeleton>);
  $ballot_skeleton = q(<BallotSkeleton>
                       <ElectionID>
                         Hunt the Duplicate Answer Marks for fun and profit
                       </ElectionID>
                       <PrecinctID>
                         87th
                       </PrecinctID>
                       )
    . $question_skeleton
      . q(</BallotSkeleton>);
  eval {
    VHTI::gen_blank_ballot::generate_blank_ballot ($ballot_skeleton,
                                                   $cep_tree->format_as_text (),
                                                   ALPHABET_ENCODING);
  };
  like ($@, qr(MALFORMED_INTEGER), "properly detects non-integer in NumAns attribute");
}

use VHTI::gen_verification_code;
{
  eval {
    VHTI::gen_verification_code::generate_verification_code (snarf ("$FindBin::Bin/../examples/DRE/vvks.xml"),
                                                             $bee_bee_tree->format_as_text (),
                                                             q(<BallotSequenceNumber Encoding="DEC">123</BallotSequenceNumber>),
                                                             q(<AnswerReference>you'll never find me</AnswerReference>),
                                                             10,
                                                             "<AlphabetEncoding>DEC</AlphabetEncoding>");
  };

  like ($@, qr(NO_MATCHING_ANSWER_REF), "properly detects bogus answer ref");
}

{

  # We'll start over with a simple ballot, since the ones we've
  # created above have a lot of answers.
  my $bs_tree = XML_Tree->construct ("BallotSkeleton");
  {
    $bs_tree->new_element ("ElectionID")->add_characters ("1");
    $bs_tree->new_element ("PrecinctID")->add_characters ("1");
    my $qs_tree = $bs_tree->new_element ("QuestionSkeleton");
    $qs_tree->add_attribute ("NumAns", "3");
    $qs_tree->new_element ("QuestionTextStructure")->add_characters ("q1");
  }
  my $bb_tree = XML_Tree->new (VHTI::gen_blank_ballot::generate_blank_ballot ($bs_tree->format_as_text (),
                                                                              $cep_tree->format_as_text (),
                                                                              ALPHABET_ENCODING));


  my $question_tree = $bb_tree->e ("BallotQuestion");

  # Now clobber the last answer's AnswerReference, making it the same
  # as the second one's.

  # This is slightly subtle.  We originally put *three* answers in our
  # ballot skeleton because we want the duplication to involve answers
  # *other* than the one whose answer ref we're passing in to
  # generate_verification_code.  That is, we're insisting that that
  # function examine the entire blank ballot for duplicates, not just
  # the one answer whose ref we're passing it.  So we pass in the ref
  # of the first question -- and that ref appears only once, which is
  # correct -- but the other two questions share their own ref.
  {
    my $second_answer = $question_tree->e ("BallotAnswer", 1);
    my $third_answer  = $question_tree->e ("BallotAnswer", 2);

    $third_answer->add_attribute ("AnswerReference", $second_answer->attribute ("AnswerReference"));
  }

  eval {
    VHTI::gen_verification_code::generate_verification_code (snarf ("$FindBin::Bin/../examples/DRE/vvks.xml"),
                                                             $bb_tree->format_as_text (),
                                                             q(<BallotSequenceNumber Encoding="DEC">123</BallotSequenceNumber>),
                                                             XML_Tree->construct ("AnswerReference")->add_characters ($question_tree->e ("BallotAnswer")->attribute ("AnswerReference"))->format_as_text (),
                                                             10,
                                                             "<AlphabetEncoding>DEC</AlphabetEncoding>");
  };

  like ($@, qr(DUPLICATE_ANSWER_REF), "properly detects duplicate answer ref");
}

{
  # Ensure that both the ballot skeleton, and the crypto election
  # parameters, affect the generated answer marks.
  sub answer_marks {
    my $ballot_skeleton_xml = shift;
    my $cep_xml = shift;
    snarf_answer_marks (XML_Tree->new (VHTI::gen_blank_ballot::generate_blank_ballot ($ballot_skeleton_xml,
                                                                                      $cep_xml,
                                                                                      ALPHABET_ENCODING)));
  }

  sub ballot_skeleton_with_whitespace {
    my $whitespace = shift;
    $whitespace = '' unless defined ($whitespace);
    qq(<BallotSkeleton> <ElectionID> 1 </ElectionID> <PrecinctID> 87 </PrecinctID>
    <QuestionSkeleton NumAns="2">
        <QuestionTextStructure> q1 </QuestionTextStructure> </QuestionSkeleton>
      $whitespace
      </BallotSkeleton>);
  }
  sub cep_with_whitespace {
    my $whitespace = shift;
    $whitespace = '' unless defined ($whitespace);
    qq(<?xml version="1.0" encoding="utf-8" ?>
<CryptoElectionParameters><CryptoGroupParameters><ElectionModulus Encoding="DEC">47</ElectionModulus>
<ElectionSubgroupModulus Encoding="DEC">23</ElectionSubgroupModulus>
<ElectionSubgroupMember Encoding="DEC">17</ElectionSubgroupMember>
</CryptoGroupParameters>
    $whitespace
    <CryptoTabulationParameters><ElectionPublicKey Encoding="DEC">7</ElectionPublicKey><NumAuth>1</NumAuth><Threshold>1</Threshold><KeyShareCommitment Encoding="DEC" AuthFingerprint="0">7</KeyShareCommitment></CryptoTabulationParameters></CryptoElectionParameters>
);
  }

  my $am_0 = join (',', sort keys %{answer_marks (ballot_skeleton_with_whitespace ("") , cep_with_whitespace (""))});
  my $am_1 = join (',', sort keys %{answer_marks (ballot_skeleton_with_whitespace (" "), cep_with_whitespace (""))});
  my $am_2 = join (',', sort keys %{answer_marks (ballot_skeleton_with_whitespace (" "), cep_with_whitespace (" "))});

  isnt ($am_0, $am_1, "ballot skeleton affects answer marks");
  isnt ($am_1, $am_2, "Crypto Election Paramaeters affect answer marks");
}
