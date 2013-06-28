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
use Data::Dumper;
use Getopt::Std;

use FindBin;
use lib "$FindBin::Bin/../../../../toast/modules";
use XML_Tree;

use VHTI;
use VHTI::gen_bsns;
use VHTI::gen_vvdict;
use VHTI::support;

use misc;
use constants;

VHTI::set_error_mode('CROAK');

sub trim {
  my @out = @_;
  for (@out) {
    s/^\s+//;
    s/\s+$//;
  }
  return wantarray ? @out : $out[0];
}

use files;

my $pollsite_pubkey = snarf ("pollsite-pubkey.xml");

my $sbb_xml = snarf ("sbb.xml");
my $bb_tree;

our ($opt_v);
getopt ("v");

$opt_v = 2 unless defined ($opt_v);

warn "$opt_v voters\n";

# Check the signature on sbb_xml, and at the same time retrieve the
# signed XML.  As it happens, we've already written the blank ballot
# to disk, and we *could* just snarf it in, but it's nice to check
# that signature checking is working.

{
  use VHTI::sign;

  (my $sig_check_result,my $bb_xml) = VHTI::sign::check_xml ($pollsite_pubkey,
                                                              $sbb_xml,
                                                              "BlankBallot");
  die "Signed blank ballot's signature did not check ($sig_check_result)"
    unless XML_Tree->new ($sig_check_result)->characters () =~ qr(0:Success);

  $bb_tree = XML_Tree->new ($bb_xml);
}
my $questions;

foreach my $q_tree (grep {$_->name () eq "BallotQuestion"} @{$bb_tree->elements ()}) {
  my $qref = $q_tree->attribute ("QuestionReference");
  $questions->{$qref}->{title} = $q_tree->e ("QuestionTextStructure")->characters ();
  foreach my $answer_tree (grep {$_->name () eq "BallotAnswer"} @{$q_tree->elements ()}) {
    $questions->{$qref}->{answers}->{$answer_tree->attribute ("AnswerReference")}->{text} = $answer_tree->e ("AnswerTextStructure")->characters ();
  }
}

use VHTI::random;
use VHTI::genkeys;

my $random_state_xml = VHTI::random::generate_random_state (qq(<RandomSeedKey>The rain in Spain falls mainly in Seattle.</RandomSeedKey>));

my $voter_roll_tree = XML_Tree->construct ("VoterRoll");

sub voter_name {
  "Joe_Voter_#" . shift;
}

sub voter_directory {
  "voter-" . shift;
}

for (my $voters = 0;
     $voters < $opt_v;
     $voters++) {
  my $ident_info_tree = XML_Tree->construct ("IdentInfo");
  $ident_info_tree->add_characters (voter_name ($voters));
  (my $voter_private_key_xml, my $voter_pubkey_xml) = VHTI::genkeys::generate_keys ($ident_info_tree->format_as_text ());

  my $cert_tree = $voter_roll_tree->new_element ("Certificate");
  $cert_tree->add_element (XML_Tree->new ($voter_pubkey_xml));

  unsnarf ($voter_private_key_xml, voter_directory (voter_name ($voters)) . "/prvkey.xml");
}

unsnarf ($voter_roll_tree->format_as_text () . "\n", "voter-roll.xml");

my $svbs_tree = XML_Tree->construct ("SignedVotedBallots");

my @certificates = grep {$_->name () eq "Certificate"} @{$voter_roll_tree->elements ()};

my @bsns;
{
  (my $auth_ballot_sequence_numbers_xml,
   my $prov_ballot_sequence_numbers_xml,
   $random_state_xml) = VHTI::gen_bsns::generate_bsns ($bb_tree->e ("ElectionID")->format_as_text (),
                                                       $bb_tree->e ("PrecinctID")->format_as_text (),,
                                                       2 * scalar (@certificates),
                                                       2 * scalar (@certificates),
                                                       $random_state_xml);

  # TODO -- do something with the provisional BSNs?
  foreach my $bsn_tree (grep {$_->name () eq "BallotSequenceNumber"} @{XML_Tree->new ($auth_ballot_sequence_numbers_xml)->elements ()}) {
    push @bsns, ($bsn_tree);
  }
}

my $vvks_xml = snarf ("DRE/vvks.xml");

# Just for fun (and realism), randomize the order of the BSNs

srand (0);
fisher_yates_shuffle (\@bsns);

{
  my $all_bsns = XML_Tree->construct ("BallotSequenceNumbers");
  foreach (@bsns) {
    $all_bsns->add_element ($_);
  }
  unsnarf ($all_bsns->format_as_text () . "\n", "bsns.xml");
}

my $expected_tally;
my $verification_codes_by_BSN;

my $votes_cast = 0;
my $voted_bsns;
for (my $bsns_used = 0;
     $bsns_used < scalar (@bsns);
     $bsns_used++) {

  my $bsn_tree = $bsns[$bsns_used];

  # TODO -- find out if the verification codes are supposed to be
  # unique.  If so, then test that they are; if not, improve the
  # following so that it doesn't merely show that each code from the
  # receipt appears in the dictionary; it should instead show that
  # each code from the receipt appears in the dictionary *the right
  # number of times*.  For example, the receipt might consist of these
  # three codes: 14, 97, 97.  Thus we need to test that the dictionary
  # contains one "14" and two "97"s.

  my $v_dictionary;

  my $vv_dict = VHTI::gen_vvdict::generate_vote_verification_dictionary ($vvks_xml,
                                                                         $bb_tree->format_as_text (),
                                                                         $bsn_tree->format_as_text (),
                                                                         VERIFICATION_CODE_BIT_LENGTH,
                                                                         ALPHABET_ENCODING);

  if ($votes_cast < scalar (@certificates)) {

    unsnarf ($vv_dict, voter_directory (voter_name ($votes_cast)) . "/vv_dict.xml");

    my $dict_questions = 0;

    foreach my $dq_tree (grep {$_->name () eq "DictionaryQuestion"}
                         @{(XML_Tree->new ($vv_dict)->elements ())}) {
      $dict_questions++;

      foreach (@{$dq_tree->elements ()}) {
        my $dvc = xml_2_bignum ($_);
        my $aref = $_->attribute ("AnswerReference");
        $v_dictionary->{$dvc} = $aref;
      }
    }

    my $voter_pubkey_tree = $certificates[$votes_cast]->e ("GeneralPurposePublicKey");
    my $clear_text_ballot_tree = XML_Tree->construct ("ClearTextBallot");

    foreach (sort keys %$questions) {

      # We must pick exactly one answer per question.
      my $q = $_;
      my @answer_refs = keys %{$questions->{$q}->{answers}};
      my $chosen_answer_ref = $answer_refs[int (rand (@answer_refs))];

      my $answer_ref_tree = $clear_text_ballot_tree->new_element ("AnswerReference");
      $answer_ref_tree->add_characters ($chosen_answer_ref);

      # TODO -- perhaps don't update expected_tally until we've
      # successfully submitted the ballot.
      $expected_tally->{$chosen_answer_ref}->{votes}++;
      $expected_tally->{$chosen_answer_ref}->{text} = trim ($questions->{$q}->{answers}->{$chosen_answer_ref}->{text});
    }
    unsnarf ($clear_text_ballot_tree->format_as_text () . "\n", voter_directory (voter_name ($votes_cast)) . "/ctb.xml");
    unsnarf ($bsn_tree              ->format_as_text () . "\n", voter_directory (voter_name ($votes_cast)) . "/bsn.xml");

    # Vote at the pollsite.
    use VHTI::enc_ballot_pollsite;

    # check verification codes.  There are two places from which we can
    # get them -- the receipt (generate_vote_receipt_data) and the
    # dictionary (generate_vote_verification_dictionary).  We ensure
    # they match.  The codes from the dictionary can easily be paired
    # with the corresponding answer refs, but those from the receipt
    # cannot; we will check all the correspondences that we can.

    {
      my $this_voters_name = $voter_pubkey_tree->e ("IdentInfo")->characters ();
      (my $signed_voted_ballot,
       $random_state_xml) = VHTI::enc_ballot_pollsite::encrypt_ballot_pollsite ($clear_text_ballot_tree->format_as_text (),
                                                                                $bb_tree->format_as_text (),
                                                                                $bsn_tree->format_as_text (),
                                                                                $random_state_xml,
                                                                                snarf (voter_directory ($this_voters_name) . "/prvkey.xml"));

      # This is a bit redundant, seeing as how we dump the *entire* svb
      # tree after this loop finishes.  But it's convenient to have each
      # voter's svb available independently.
      unsnarf ($signed_voted_ballot, voter_directory (voter_name ($votes_cast)) . "/svb.xml");

      $voted_bsns->{xml_2_bignum ($bsn_tree) . ""}++;

      $svbs_tree->add_element (XML_Tree->new ($signed_voted_ballot));

      use VHTI::gen_vote_receipt_data;

      use VHTI::sign_receipt;

      my $unsigned_receipt = VHTI::gen_vote_receipt_data::generate_vote_receipt_data ($signed_voted_ballot,
                                                                                      $vvks_xml,
                                                                                      $bb_tree->format_as_text (),
                                                                                      $bsn_tree->format_as_text (),
                                                                                      $clear_text_ballot_tree->format_as_text (),
                                                                                      VERIFICATION_CODE_BIT_LENGTH,
                                                                                      ALPHABET_ENCODING);

      my $signed_receipt = VHTI::sign_receipt::sign_receipt ($unsigned_receipt,
                                                             snarf ("pollsite-private-key.xml"));

      warn "Cannot check SVB hash "
        . XML_Tree->new ($unsigned_receipt)->attribute ("SVBHash")
	  . " because we haven't yet documented how we hash";

      unsnarf ($unsigned_receipt, voter_directory (voter_name ($votes_cast)) . "/receipt-data.xml");
      unsnarf ($signed_receipt  , voter_directory (voter_name ($votes_cast)) . "/receipt.xml");

      my @verification_codes_from_receipt;

      my $vote_receipt_xml;

      {
        (my $sig_check_result, $vote_receipt_xml) = VHTI::sign::check_xml ($pollsite_pubkey,
                                                                           $signed_receipt,
                                                                           "VoteReceiptData");

        die "Vote receipt's signature did not check ($sig_check_result)"
          unless XML_Tree->new ($sig_check_result)->characters () =~ qr(0:Success);
      }

      foreach (@{XML_Tree->new ($vote_receipt_xml)->e ("VoteVerificationCodes")->elements ()}) {
        my $this_code = "" . xml_2_bignum ($_); # coerce the bignum into a string
        die "Receipt verification code $_ wasn't in the dictionary " . Dumper ($v_dictionary)
          unless (exists $v_dictionary->{$this_code});
        push @verification_codes_from_receipt, $this_code;
      }

      die "not exactly $dict_questions receipt codes in the verification dictionary"
        unless (scalar (@verification_codes_from_receipt) == $dict_questions);

      $verification_codes_by_BSN->{$bsn_tree->characters ()} = [@verification_codes_from_receipt];

      print STDERR "$this_voters_name voted; verification codes from receipt match those from dictionary.\n";

      $votes_cast++;
    }
  } else {
    # We've voted as many BSNs as we can, so let's put on our auditor
    # hat.
    unsnarf ($vv_dict, "dict_from_unvoted_BSN_" . xml_2_bignum ($bsn_tree) . ".xml");
  }
}
unsnarf (Data::Dumper->Dump ([$voted_bsns], [qw(voted_bsns)]), "voted-bsns.pl");
unsnarf (Data::Dumper->Dump ([$expected_tally   ], [qw(expected_tally   )]), "expected-tally.pl"              );
unsnarf (Data::Dumper->Dump ([$verification_codes_by_BSN], [qw(verification_codes_by_BSN)]), "verification-codes-by-BSN.pl");
unsnarf ($svbs_tree->format_as_text () . "\n", "svbs.xml");

update_stats ();
