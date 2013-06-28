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

use VHTI;
use VHTI::auth;
use VHTI::check_comm;
use VHTI::check_dictionary_secrets;
use VHTI::check_partial_decrypt;
use VHTI::check_pds_and_combine;
use VHTI::check_shuffle;
use VHTI::check_vc_pds_and_combine;
use VHTI::combine_dictionary_secrets;
use VHTI::enc_ballot_pollsite;
use VHTI::gen_answer_mark;
use VHTI::gen_broadcast;
use VHTI::gen_bsns;
use VHTI::gen_comm;
use VHTI::gen_dictionary_secrets;
use VHTI::gen_pre_verification_results;
use VHTI::gen_pv_results;
use VHTI::gen_seccoeff;
use VHTI::gen_secrets;
use VHTI::gen_vvdict_comm;
use VHTI::genkeys;
use VHTI::keyshare_util;
use VHTI::partial_decrypt;
use VHTI::random;
use VHTI::shuffle;
use VHTI::support;

use files;
use misc;
use constants;

use FindBin;
use lib "$FindBin::Bin/../../../../toast/modules";
use XML_Tree;

VHTI::set_error_mode('CROAK');

my $sbb_xml = snarf ("sbb.xml");
my  $bb_xml = snarf ("bb.xml");
my $ballot_signing_key = snarf ("pollsite-pubkey.xml");

my $raw_ballot_box_xml = VHTI::auth::authenticate (snarf ("svbs.xml"),
                                                   snarf ("voter-roll.xml"),
                                                   $bb_xml);

unsnarf ($raw_ballot_box_xml, "rbb.xml");


my $random_state_xml = VHTI::random::generate_random_state (qq(<RandomSeedKey>Snack-related mishap!!</RandomSeedKey>));

my $shuffled_rbb;

my $threshold = XML_Tree->new ($bb_xml)->e ("CryptoElectionParameters")->e ("CryptoTabulationParameters")->e ("Threshold")->characters ();
my $num_auth  = XML_Tree->new ($bb_xml)->e ("CryptoElectionParameters")->e ("CryptoTabulationParameters")->e ("NumAuth")->characters ();

warn "Will shuffle $threshold times";

{
  my $bbox_in = $raw_ballot_box_xml;
  my $bbox_out;

  foreach (0 .. $threshold - 1) {
    ($bbox_out, $random_state_xml, my $shuffle_validity_proof_xml) = VHTI::shuffle::shuffle ($bbox_in,
                                                                                             $random_state_xml,
                                                                                             $sbb_xml,
                                                                                             $ballot_signing_key);
    print STDERR "... shuffle #$_ ...\n";

    my $check_answer_result =
      XML_Tree->new(VHTI::check_shuffle::check_shuffle ($bbox_in,
                                                        $bbox_out,
                                                        $sbb_xml,
                                                        $ballot_signing_key,
                                                        $shuffle_validity_proof_xml))->characters ();
    die "Proofs didn't check! $check_answer_result"
      unless ($check_answer_result =~ m(success)i);

    # TODO: Consider storing these in a subdirectory corresponding to
    # the shuffler, even though they're not secret.

    unsnarf ($bbox_out, "shuffled-rbb-#$_.xml");
    unsnarf ($shuffle_validity_proof_xml, "shuffle-validity-proof-#$_.xml");

    $bbox_in = $bbox_out;
  }

  $shuffled_rbb = $bbox_out;
}


my $partially_decrypted_bb_tree = XML_Tree->construct ("PartiallyDecryptedBallotBox");
$partially_decrypted_bb_tree->add_element (XML_Tree->new ($shuffled_rbb));
$partially_decrypted_bb_tree->new_element ("AuthorityPartialDecrypts");

# Instead of always using the first t authorities, we pick them at
# random, sort of -- we always let authority#0 do a decryption
# (because some of the tests have a hard-coded path to
# `auth0/partial-decrypt.xml'); the others we choose randomly.
srand (0);
{
  my @randomly_permuted_auth_indices = (1 .. $num_auth);
  fisher_yates_shuffle (\@randomly_permuted_auth_indices);
  unshift @randomly_permuted_auth_indices, 0;

  for (my $decrypts_to_do = $threshold;
       $decrypts_to_do > 0;
       $decrypts_to_do--) {

    my $which_authority = $randomly_permuted_auth_indices[$decrypts_to_do - 1];
    warn "randomly-chosen authority $which_authority is about to do partial_decrypt";

    my $committed_authority_xml = snarf ("committed-auth-$which_authority.xml");
    my $secret_share_xml        = snarf (           "auth$which_authority/secret-share.xml");
    (my $authority_partital_decrypt_xml, $random_state_xml)
      = VHTI::partial_decrypt::partial_decrypt ($shuffled_rbb,
                                                $sbb_xml,
                                                $ballot_signing_key,
                                                $committed_authority_xml,
                                                $secret_share_xml,
                                                $random_state_xml);

    $partially_decrypted_bb_tree->e ("AuthorityPartialDecrypts")->add_element (XML_Tree->new ($authority_partital_decrypt_xml));
    unsnarf ($authority_partital_decrypt_xml, "auth$which_authority/partial-decrypt.xml");
  }

  unsnarf ($partially_decrypted_bb_tree->e ("AuthorityPartialDecrypts")->format_as_text (),
           "auth-partial-decrypts.xml");
}

unsnarf ($partially_decrypted_bb_tree->format_as_text () . "\n", "partially-decrypted-bb.xml");

(my $clear_text_ballots, my $combine_partial_decrypt_result)
  = VHTI::check_pds_and_combine::check_partial_decrypts_and_combine ($sbb_xml,
                                                                     $ballot_signing_key,
                                                                     $partially_decrypted_bb_tree->format_as_text ());
{
  my $status_string = XML_Tree->new ($combine_partial_decrypt_result)->characters ();
  die "check_partial_decrypts_and_combine failed: $status_string"
    unless $status_string =~ qr(Success);
}

# Just out of paranoia, mess with the partically-decrypted ballot box,
# and make sure that `check_partial_decrypts_and_combine' notices.
# But do this only if q is fairly large, since otherwise there'd be a
# real chance that it'll give a false positive.

if (length (xml_2_bignum (XML_Tree->new (snarf ("cep.xml"))->e ("CryptoGroupParameters") ->e ("ElectionSubgroupModulus")) . "")
    >= 12) {
  my $first_constant_tree = $partially_decrypted_bb_tree
    ->e ('AuthorityPartialDecrypts')
      ->e ('AuthorityPartialDecrypt')
        ->e ('BallotBoxPartialDecrypt')
          ->e ( 'BallotPartialDecrypt')
            ->e ('AnswerPartialDecrypt')
              ->e ('ConstantVal');
  my $constant_bignum = xml_2_bignum ($first_constant_tree);
  $first_constant_tree->remove_all_characters ();
  $first_constant_tree->add_characters ($constant_bignum - 1);

  warn "Don't be alarmed by a failure message below; it is intentional\n";
  (my $dummy, my $hopefully_a_failure_code) = VHTI::check_pds_and_combine::check_partial_decrypts_and_combine ($sbb_xml,
                                                                                                               $ballot_signing_key,
                                                                                                               $partially_decrypted_bb_tree->format_as_text ());
  {
    my $status_string = XML_Tree->new ($hopefully_a_failure_code)->characters ();
    die "check_partial_decrypts_and_combine unexpectedly succeeded: $status_string"
      unless $status_string =~ qr(Failure);
  }

}

{
  my $actual_tally;

  foreach my $ctb (@{XML_Tree->new ($clear_text_ballots)->elements ()}) {

    foreach my $answer_ref (@{$ctb->elements ()}) {

      $actual_tally->{$answer_ref->characters ()}++;
    }
  }

  my $expected_tally;
  eval (snarf ("expected-tally.pl"));
  foreach (sort keys %$expected_tally) {
    my $actual_votes   = $actual_tally->{$_};
    my $expected_votes = $expected_tally->{$_}->{votes};
    die "Expected $expected_votes for answer ref $_; got $actual_votes"
      unless ($expected_votes == $actual_votes);
  }

  print STDERR "Woohoo!  Actual tally matches expected tally!\n";
  print STDERR Data::Dumper->Dump ([$expected_tally], [qw(expected_tally)]);
}

# Now generate the verification codes for each ballot in the box

my $pre_vc_boxes_tree = XML_Tree->construct ("PreVerificationCodeBoxes");

my $svbs_xml = snarf ("svbs.xml");

my $all_vvks = XML_Tree->new (snarf ("DRE/vvks.xml"));
foreach my $vvk_tree (@{$all_vvks->elements ()}) {
  print STDERR "Generating pre-verification code box for vote verification key ",
    $vvk_tree->characters (),
      " ...";

  $pre_vc_boxes_tree->add_element (XML_Tree->new (VHTI::gen_pre_verification_results::generate_pre_verification_results ($vvk_tree->format_as_text (),
                                                                                                                         $svbs_xml,
                                                                                                                         $sbb_xml,
                                                                                                                         $ballot_signing_key)));
  print STDERR " done\n";
}

unsnarf ($pre_vc_boxes_tree->format_as_text (), "pre-vc-boxes.xml");

my $auth_partial_decrypts_tree = XML_Tree->construct ("AuthorityPartialDecrypts");
my $trustee_revealed_dictionary_secrets_box = XML_Tree->construct ("TrusteeRevealedDictionarySecretsBox");

foreach my $committed_auth_xml (map { snarf $_ } glob "committed-auth-[0-9]*.xml") {
  my $auth_tree = XML_Tree->new($committed_auth_xml)->e ("Authority");
  my $fingerprint = $auth_tree->attribute ("AuthFingerprint");
  my $subdirectory = "auth" . $fingerprint;

  (my $auth_partial_decrypt_of_verifications, $random_state_xml)
    = VHTI::gen_pv_results::generate_partial_verification_results ($pre_vc_boxes_tree->format_as_text (),
                                                                   $sbb_xml,
                                                                   $ballot_signing_key,
                                                                   $committed_auth_xml,
                                                                   snarf ($subdirectory . "/secret-share.xml"),
                                                                   $random_state_xml);
  $auth_partial_decrypts_tree->add_element (XML_Tree->new ($auth_partial_decrypt_of_verifications));
}

{
  my $bsns_xml = snarf ("bsns.xml");
  my $voted_bsns; eval (snarf ("voted-bsns.pl"));
  my $unvoted_bsns;
  my $all_bsns;

  foreach (@{XML_Tree->new ($bsns_xml)->elements ()}) {
    $all_bsns->{xml_2_bignum ($_) . ""}++;
  }

  my @trustee_directories = glob "trustee-[0-9]*/";
  for (my $trustees_processed = 0;
       $trustees_processed < @trustee_directories;
       $trustees_processed++) {
    my $trustee = $trustee_directories[$trustees_processed];
    $trustee =~ s{/$}();      # lose trailing slash
    my $this_vvk = snarf ("$trustee/vvk.xml");
    my $private_key = snarf ("$trustee/private-key");

    # We're using the same authorites to tabulate and to do the trustee thing.
    my $auth = snarf ("auth" . ($trustees_processed % $num_auth) . ".xml");
    my $trustee_dictionary_commitments =
      (XML_Tree->new (VHTI::gen_vvdict_comm::generate_vvdict_commits
                      ($auth,
                       $private_key,
                       $this_vvk,
                       $bb_xml,
                       $bsns_xml)));

    unsnarf ($trustee_dictionary_commitments->format_as_text () . "\n", "${trustee}-dict_comm.xml");

    my $revealed_thingo = XML_Tree->new (VHTI::gen_dictionary_secrets::generate_dictionary_secrets
                                         ($svbs_xml,
                                          $auth,
                                          $private_key,
                                          $this_vvk,
                                          $bb_xml,
                                          $bsns_xml));

    unsnarf ($revealed_thingo->format_as_text () . "\n", "${trustee}-revealed_dict_secrets.xml");

    foreach (grep {$_->name () eq "BSNRevealedDictionarySecrets"} @{$revealed_thingo->elements ()}) {
      $unvoted_bsns->{xml_2_bignum ($_->e ("BallotSequenceNumber")) . ""}++;
    }
    $trustee_revealed_dictionary_secrets_box->add_element ($revealed_thingo) ;

    my $check_results = VHTI::check_dictionary_secrets::check_dictionary_secrets ($revealed_thingo->format_as_text (),
                                                                                  $trustee_dictionary_commitments->format_as_text (),
                                                                                  snarf ("${trustee}-pubkey.xml"),
                                                                                  $bb_xml);
    die "check_dictionary_secrets failed: $check_results"
      unless $check_results =~ qr(Success);
    warn "woo hoo -- check_results for trustee $trustee succeeded\n";
  }

  foreach (keys %$all_bsns) {
    my $appears_in_voted            = exists ($voted_bsns  ->{$_});
    my $appears_in_revealed_secrets = exists ($unvoted_bsns->{$_});
    die "BSN $_ appears in neither the voted BSNs, nor the revealed dictionary secrets"
      if (!$appears_in_revealed_secrets && !$appears_in_voted);

    die "BSN $_ appears in both the voted BSNs, nor the revealed dictionary secrets"
      if ($appears_in_revealed_secrets && $appears_in_voted);
  }
}

# Check the statements against dictionaries of BSNs that weren't
# voted.
{
  foreach my $statement_tree (@{XML_Tree->new (VHTI::combine_dictionary_secrets::combine_dictionary_secrets
                                               ($trustee_revealed_dictionary_secrets_box->format_as_text (),
                                                $bb_xml,
                                                VERIFICATION_CODE_BIT_LENGTH,
                                                ALPHABET_ENCODING))->elements ()}) {
    my $statement_xml = $statement_tree->format_as_text ();

    # It looks pointless to parse this file and then immediately
    # unparse it.  But doing so ensures that it includes the `<?xml
    # version blah?>' header.
    my $dict_from_DRE = XML_Tree->new (snarf ("dict_from_unvoted_BSN_"
                                              . xml_2_bignum ($statement_tree->e ("BallotSequenceNumber"))
                                              . ".xml"))->format_as_text ();

    die "These are not identical: `$dict_from_DRE' <-> `$statement_xml'"
      unless ($dict_from_DRE eq $statement_xml);
    print STDERR "Hooray, the trustees didn't cheat -- unvoted dictionary matches statement\n";
  }
}
unsnarf ($trustee_revealed_dictionary_secrets_box->format_as_text () . "\n", "trustee_revealed_dict_secrets_box.xml");
unsnarf ($auth_partial_decrypts_tree->format_as_text (),
         "partial-decrypts-4vc.xml");

use constants;

(my $verification_statements_xml, my $result_xml)
  = VHTI::check_vc_pds_and_combine::check_vcode_partial_decrypts_and_combine ($pre_vc_boxes_tree->format_as_text (),
                                                                              $auth_partial_decrypts_tree->format_as_text (),
                                                                              $svbs_xml,
                                                                              $sbb_xml,
                                                                              $ballot_signing_key,
                                                                              VERIFICATION_CODE_BIT_LENGTH,
                                                                              ALPHABET_ENCODING);

unsnarf ($verification_statements_xml, "verification-statements.xml");
{
  my $result = XML_Tree->new ($result_xml)->characters ();
  die "check_verification_code_partial_decrypts_and_combine failed ($result)"
    unless ($result =~ m(success)i);
}

my $verification_codes_by_BSN; eval (snarf ("verification-codes-by-BSN.pl"));
my @verification_statements_trees = @{XML_Tree->new ($verification_statements_xml)->elements ()};

while (@verification_statements_trees) {

  my $this_verification_statement_tree = shift @verification_statements_trees;
  my $this_bsn = $this_verification_statement_tree->e ("BallotSequenceNumber")->characters ();

  my $statement_codes   = join (' ', sort map {xml_2_bignum ($_)}
                                grep {$_->name () eq "VoteVerificationCode"}
                                @{$this_verification_statement_tree->elements ()}
                               );
  my $receipt_codes = join (' ', sort @{$verification_codes_by_BSN->{$this_bsn}});

  die ("Verification codes from receipt for BSN $this_bsn ($receipt_codes)\n".
       "don't match codes from statement          ($statement_codes)")
    unless $receipt_codes eq $statement_codes;
}

print STDERR "Verification codes from receipts match those from verification statements.\n";

update_stats ();
