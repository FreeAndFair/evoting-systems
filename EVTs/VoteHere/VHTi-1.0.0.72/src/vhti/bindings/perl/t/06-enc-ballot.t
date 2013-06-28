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
use Test::More tests => 12;

BEGIN { use_ok('VHTI') };
BEGIN { use_ok('VHTI::enc_ballot_pollsite') };

use FindBin;
use lib ("$FindBin::Bin", "$FindBin::Bin/../examples", "$FindBin::Bin/../../../../toast/modules");
use common;
use XML_Tree;
use POSIX;
use files;
use pscommon;

use warnings;
use strict;
use Data::Dumper;

use VHTI::random;
use VHTI::sign;

my $random_state_xml = VHTI::random::generate_random_state (qq(<RandomSeedKey>Hamburgers!  The cornerstone of any nutritious breakfast.</RandomSeedKey>));

my $bsn = q(<BallotSequenceNumber Encoding="DEC">1</BallotSequenceNumber>);
my $prvkey = snarf ("$FindBin::Bin/../examples/voter-Joe_Voter_#0/prvkey.xml");
my $bb_tree = XML_Tree->new (snarf ("$FindBin::Bin/../examples/bb.xml"));

my $ballot_signing_key = snarf ("$FindBin::Bin/../examples/pollsite-private-key.xml");
my $pollsite_pubkey = snarf ("$FindBin::Bin/../examples/pollsite-pubkey.xml");

my $num_questions;
for ($num_questions = 0;
     $bb_tree->e ("BallotQuestion", $num_questions);
     $num_questions++) {
}

if ($num_questions < 2) {
  warn "Skipping a test because your blank ballot has only one question";
  pass ();
} else {
  my $ctb_tree = XML_Tree->construct ("ClearTextBallot");
  $ctb_tree->new_element ("AnswerReference")->add_characters ("A0");
  go ($bb_tree,
      $ctb_tree,
      qr(WRONG_NUMBER_OF_ANSWERS), "proper exception with too few answer refs");
}

# Likewise with too many answers.
{
  my $ctb_tree = XML_Tree->construct ("ClearTextBallot");
  add_some_answer_refs ($ctb_tree,
                        $num_questions + 1);
  go ($bb_tree,
      $ctb_tree,
      qr(WRONG_NUMBER_OF_ANSWERS), "proper exception with too many answer refs");
}

{
  my $ctb_tree = XML_Tree->construct ("ClearTextBallot");
  add_some_answer_refs ($ctb_tree,
                        $num_questions);
  $ctb_tree->e ("AnswerReference")->remove_all_characters ();
  go ($bb_tree,
      $ctb_tree,
      qr(EMPTY_ANSWER_REF), "proper exception with empty answer ref");

  $ctb_tree->e ("AnswerReference")->add_characters ("entirely invalid answer ref");
  go ($bb_tree,
      $ctb_tree,
      qr(NO_MATCHING_ANSWER_REF), "proper exception with bogus answer ref");
}

{
  my $ctb_tree = XML_Tree->construct ("ClearTextBallot");
  add_some_answer_refs ($ctb_tree,
                        $num_questions);

  foreach my $elt qw(ElectionModulus ElectionSubgroupModulus ElectionSubgroupMember) {
    try_with_non_numeric ($bb_tree,
                          $ctb_tree,
                          "CryptoElectionParameters", "CryptoGroupParameters", $elt);
  }

  foreach my $elt qw(ElectionPublicKey) {
    try_with_non_numeric ($bb_tree,
                          $ctb_tree,
                          "CryptoElectionParameters", "CryptoTabulationParameters", $elt);
  }

  try_with_non_numeric ($bb_tree,
                        $ctb_tree,
                        "BallotQuestion", "BallotAnswer", "AnswerMark");
}

{
  my $ctb_tree = XML_Tree->construct ("ClearTextBallot");
  add_some_answer_refs ($ctb_tree,
                        $num_questions);

  # Check that the function detects numbers which aren't members of the
  # election subgroup.

  go (corrupted_blank_ballot ($bb_tree),
      $ctb_tree,
      qr(NOT_SUBGROUP_MEMBER), "detect answer marks that aren't members of the election subgroup");
}

sub try_with_non_numeric {
  my $original = shift;

  my $bee_bee_tree = XML_Tree->new ($original->format_as_text ());

  my $ctb_tree = shift;

  my $elt = elt_by_path ($bee_bee_tree, @_);

  $elt->remove_all_characters ();
  $elt->add_characters ("Betcha can't parse me as a number!");

  go ($bee_bee_tree,
      $ctb_tree,
      qr(BADLY_FORMED_NUMBER), "proper exception with non-numeric $_[-1]");
}

sub go {
  my $bee_bee_tree = shift;
  my $ctb_tree = shift;
  my $regexp = shift;
  my $message = shift;

  eval {
    VHTI::enc_ballot_pollsite::encrypt_ballot_pollsite ($ctb_tree->format_as_text (),
                                                        $bee_bee_tree->format_as_text (),
                                                        $bsn,
                                                        $random_state_xml,
                                                        $prvkey);
  };
  like ($@, $regexp, "(encrypt_ballot_pollsite): $message");

  {
    my $unsigned_xml = $bee_bee_tree->format_as_text ();
    my $signed_xml   = VHTI::sign::sign_xml ($ballot_signing_key,
                                             $unsigned_xml);
    my $ctb_xml      = $ctb_tree->format_as_text ();
    #warn $signed_xml;
  }
}
