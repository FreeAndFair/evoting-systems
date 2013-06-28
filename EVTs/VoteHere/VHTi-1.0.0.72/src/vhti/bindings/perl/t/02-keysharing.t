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

use Test::More tests => 38;

use warnings;
use strict;
use Data::Dumper;

use VHTI;
use VHTI::gen_seccoeff;
use VHTI::keyshare_util;
use VHTI::random;
use VHTI::gen_broadcast;
use VHTI::gen_comm;
use VHTI::gen_pubkey;
use VHTI::check_comm;
use VHTI::gen_secrets;

use FindBin;
use lib ("$FindBin::Bin", "$FindBin::Bin/../examples", "$FindBin::Bin/../../../../toast/modules");
use common;
use files;
use XML_Tree;

chdir ("$FindBin::Bin")
  or die "Can't cd to $FindBin::Bin: $!; stopped";

my $g_auth_xml = snarf ("../examples/auth0.xml");
my $random_state_xml = VHTI::random::generate_random_state (qq(<RandomSeedKey/>));

sub test {
  my $num_auths = shift;
  my $threshold = shift;
  my $seed_tree = XML_Tree->construct ("SeedParameters");
  $seed_tree->new_element ("NumAuth")  ->add_characters ($num_auths);
  $seed_tree->new_element ("Threshold")->add_characters ($threshold);

  (my $kgp_xml, $random_state_xml) = VHTI::keyshare_util::create_keygen_parameters ($seed_tree->format_as_text (), $random_state_xml);

  (my $private_key, my $authority, $random_state_xml) = VHTI::keyshare_util::create_authority (qq(10), $kgp_xml, $random_state_xml, "");
  (my $secret_coefficients_xml, $random_state_xml) = VHTI::gen_seccoeff::generate_secret_coefficients ($kgp_xml,
                                                                                                       $g_auth_xml,
                                                                                                       $random_state_xml);

  my $sc_tree = XML_Tree->new ($secret_coefficients_xml);

  {
    my $num_coeffs = $sc_tree->num_elements ();

    is ($num_coeffs, $threshold, "with $num_auths authorites, number of coefficients ($num_coeffs) equals threshold ($threshold)");
  }
  my $subgroup_modulus = XML_Tree->new ($kgp_xml)->e ("CryptoGroupParameters")->e ("ElectionSubgroupModulus")->characters ();

  my $bad_thetas = 0;
  {
    for (my $elts_examined = 0;
         $elts_examined < $sc_tree->num_elements ();
         $elts_examined++) {
      my $elt = $sc_tree->element ($elts_examined);

      my $theta = $elt->characters ();
      $bad_thetas++ unless $theta < $subgroup_modulus;
    }
  }
  is ($bad_thetas, 0, "All thetas are in Z_q");

  (my $broadcast_value_xml, undef) = VHTI::gen_broadcast::generate_broadcast ($kgp_xml,
                                                                              $secret_coefficients_xml,
                                                                              $random_state_xml);

  # Now interchange the small thetas, and ensure we get the same
  # broadcast value.

  my $original_first_small_theta = $sc_tree->e ("SmallTheta", 0)->format_as_text ();
  $sc_tree->delete_element (0);
  $sc_tree->add_element (XML_Tree->new ($original_first_small_theta));

  (my $new_broadcast_value, $random_state_xml) = VHTI::gen_broadcast::generate_broadcast ($kgp_xml,
                                                                                          $sc_tree->format_as_text (),
                                                                                          $random_state_xml);

  ok (bvs_equal ($broadcast_value_xml, $new_broadcast_value), "Order of appearance of small thetas doesn't matter");

  if ($threshold > 1) {
    # Make sure it rejects the secret coefficients if two small thetas
    # have the same order.
    eval {
      $sc_tree->element (0)->add_attribute ("Order", "0");
      $sc_tree->element (1)->add_attribute ("Order", "0");
      VHTI::gen_broadcast::generate_broadcast ($kgp_xml,
                                               $sc_tree->format_as_text (),
                                               $random_state_xml)
      };
    like ($@, qr(DUPLICATE_ORDER), "rejects duplicate orders");

    # Make sure generate_secret pukes if the number of secret
    # coefficients isn't equal to the tabulation threshold.  We'll
    # nuke all but one secret.
    {
      my $corrupted_sc_tree = XML_Tree->new ($secret_coefficients_xml);

      for (my $small_thetas_to_delete = $threshold - 1;
          $small_thetas_to_delete > 0;
           $small_thetas_to_delete--) {
        $corrupted_sc_tree->delete_element (0);
      }

      eval {
        VHTI::gen_secrets::generate_secret ($kgp_xml,
                                            $authority,
                                            $corrupted_sc_tree->format_as_text ());
      };
    }
    like ($@, qr(WRONG_NUMBER_LITTLE_THETAS), "generate_secret detects wrong number of secrets");

  } else {
    foreach (1..2) { pass ("Skipping a test because our threshold is only one") };
  }
}


test (4, 4);
test (3, 2);
test (2, 1);
test (1, 1);

my $g_kgp_xml = snarf ("../examples/kgp.xml");
my $g_threshold;
my $g_num_auth;
{
  my $kgp_tree = XML_Tree->new ($g_kgp_xml);
  $g_threshold = $kgp_tree->e ("Threshold")->characters ();
  $g_num_auth  = $kgp_tree->e ("NumAuth"  )->characters ();
}
my $g_pws_xml = snarf ("../examples/auth0/pws.xml");

# Twiddle the BigThetas, and see if generate_commitment notices.
my $original_bvs_tree = XML_Tree->new (snarf ("../examples/broadcast-values.xml"));

use Math::BigInt;

my $generator = XML_Tree->new (snarf ("../examples/cgp.xml"))->e ("ElectionSubgroupMember")->characters ();

for (my $elt_index = 0;
     $elt_index < $g_threshold;
     $elt_index++) {

  if (1 == $generator) {
    pass (q(Skipping the twiddling of BigThetas, because the "generator" is 1));
  } else {
    my $corrupted_tree = XML_Tree->new ($original_bvs_tree->format_as_text ());
    my $elt = $corrupted_tree->e ("BroadcastValue")->e ("BigTheta", $elt_index);
    my $corrupted_number = xml_2_bignum ($elt->format_as_text ());
    {
      # "corrupt" the number by multiplying it by the subgroup
      # generator.  This ensures that we get
      # *) a different number :), and
      # *) a number that is still an element of the subgroup

      $corrupted_number *= $generator;
    }
    $elt->remove_all_characters ();
    $elt->add_characters ($corrupted_number);
    $elt->add_attribute ("Encoding", "DEC");
    gen_com (qr(PAIRWISE_SECRET_DIDNT_CHECK),
             $corrupted_tree->format_as_text (),
             $g_pws_xml,
             "twiddled " . $elt->name () . " element");
  }
}

# Similarly twiddle the pairwise secrets.
my $original_pws_tree = XML_Tree->new (snarf ("../examples/auth0/pws.xml"));

for (my $elt_index = 0;
     $elt_index < $original_pws_tree->num_elements ();
     $elt_index++) {

  if (1 == $generator) {
    pass (q(Skipping the twiddling of pairwise secrets, because the "generator" is 1));
  } else {
    my $corrupted_tree = XML_Tree->new ($original_pws_tree->format_as_text ());
    my $elt = $corrupted_tree->e ("PairwiseSecret", $elt_index);
    my $corrupted_number = xml_2_bignum ($elt->format_as_text ());
    $corrupted_number *= $generator;
    $elt->remove_all_characters ();
    $elt->add_characters ($corrupted_number);
    $elt->add_attribute ("Encoding", "DEC");
    gen_com (qr(PAIRWISE_SECRET_DIDNT_CHECK),
             $original_bvs_tree->format_as_text (),
             $corrupted_tree->format_as_text (),
             "twiddled " . $elt->name () . " element");
  }
}

# Twiddle the Omega and the Something (i.e., the zero-knowledge
# proof), and see if generate_public_key notices.
foreach (qw(Omega Something)) {

  if (1 == $generator) {
    pass (q(Skipping the twiddling of pairwise secrets, because the "generator" is 1));
  } else {
    my $corrupted_tree = XML_Tree->new ($original_bvs_tree->format_as_text ());
    my $elt = $corrupted_tree->e ("BroadcastValue")->e ($_);
    my $corrupted_number = xml_2_bignum ($elt->format_as_text ());
    $corrupted_number *= $generator;
    $elt->remove_all_characters ();
    $elt->add_characters ($corrupted_number);
    $elt->add_attribute ("Encoding", "DEC");
    gen_pub (qr(COMMITTMENT_ZKP_PROOF_DIDNT_CHECK),
             $corrupted_tree->format_as_text (),
             "twiddled $_ element");
  }
}

# Too many/too few BIG_THETAs in BroadcastValue
if ($g_threshold > 1) {
  my $wrong_number_big_thetas = XML_Tree->new ($original_bvs_tree->format_as_text ());
  $wrong_number_big_thetas->e ("BroadcastValue")->add_element_before (bogus_big_theta (), $g_threshold);
  my $wrong_broadcasts = XML_Tree->new ($original_bvs_tree->format_as_text ());
  $wrong_broadcasts->add_element_before ($original_bvs_tree->e ("BroadcastValue"));

  gen_com (qr(WRONG_NUMBER_OF_BIG_THETAS),
           $wrong_number_big_thetas->format_as_text (),
           $g_pws_xml,
           "too many big thetas");
  gen_pub (qr(WRONG_NUMBER_OF_BIG_THETAS),
           $wrong_broadcasts->format_as_text (),
           "too many big thetas");
  $wrong_number_big_thetas->e ("BroadcastValue")->delete_element ($g_threshold);
  $wrong_number_big_thetas->e ("BroadcastValue")->delete_element (0);
  $wrong_broadcasts->delete_element (0);
  $wrong_broadcasts->delete_element (0);
  gen_com (qr(WRONG_NUMBER_OF_BIG_THETAS),
           $wrong_number_big_thetas->format_as_text (),
           $g_pws_xml,
           "too few big thetas");
  gen_pub (qr(WRONG_NUMBER_OF_BIG_THETAS),
           $wrong_broadcasts->format_as_text (),
           "too few big thetas");
} else {
  foreach (1..4) { pass ("Skipping some tests because our threshold is only one") };
}

# Too many/too few secrets
if ($g_num_auth > 1) {

    my $corrupted_tree  = XML_Tree->new ($g_pws_xml);
    my $extra_secret = XML_Tree->construct ("PairwiseSecret");
    $extra_secret->add_attribute ("Encoding", "DEC");
    $extra_secret->add_attribute ("ToID", "0");
    $extra_secret->add_attribute ("FromID", $g_num_auth + 1);
    $extra_secret->add_characters ("1");

    $corrupted_tree->add_element ($extra_secret);

    my $bvs_xml = snarf ("../examples/broadcast-values.xml");
    gen_com (qr(NUMBER_OF_SECRETS_NOT_EQUAL_TO_NUMBER_OF_AUTHORITIES),
             $bvs_xml,
             $corrupted_tree->format_as_text (),
             "too many secrets");
    $corrupted_tree->delete_element (0);
    $corrupted_tree->delete_element (0);
    gen_com (qr(NUMBER_OF_SECRETS_NOT_EQUAL_TO_NUMBER_OF_AUTHORITIES),
             $bvs_xml,
             $corrupted_tree->format_as_text (),
             "too few secrets");

  {
    my $twiddled_ksc = XML_Tree->new (snarf ("../examples/auth0-ksc.xml"));
    $twiddled_ksc->add_attribute ("AuthFingerprint", "1");
    check_comm (qr(Fail),
                $g_kgp_xml,
                snarf ("../examples/broadcast-values.xml"),
                $twiddled_ksc->format_as_text (),
               "mismatched authority fingerprint");
  }

  {
    my $twiddled_kgp = XML_Tree->new ($g_kgp_xml);
    my $old_thresh = $twiddled_kgp->e ("Threshold")->characters ();
    $twiddled_kgp->e ("Threshold")->remove_all_characters ();
    $twiddled_kgp->e ("Threshold")->add_characters ($old_thresh + 1);
    check_comm (qr(Fail),
                $twiddled_kgp->format_as_text (),
                snarf ("../examples/broadcast-values.xml"),
                snarf ("../examples/auth0-ksc.xml"),
                "not exactly NumAuth * threshold big thetas"
               );
  }

  # Duplicate FromID
  $corrupted_tree = XML_Tree->new ($g_pws_xml);
  $corrupted_tree->e ("PairwiseSecret", 1)->add_attribute ("FromID",
                                                          $corrupted_tree->e ("PairwiseSecret", 0)->attribute ("FromID"));
  gen_com (qr(DUPLICATE_SECRET),
          $bvs_xml,
          $corrupted_tree->format_as_text (),
          "duplicate secret");

  $corrupted_tree = XML_Tree->new ($g_pws_xml);
  $corrupted_tree->e ("PairwiseSecret", 1)->add_attribute ("FromID", "12345");
  gen_com (qr(NO_SECRET_FROM_AUTHORITY),
          $bvs_xml,
          $corrupted_tree->format_as_text (),
          "no secret from some authority or other");
} else {
  foreach (1..6) { pass ("Skipping a test because NumAuth is only one") };
}

sub gen_com {
  my $expected_exception_regexp = shift;
  my $bvs_xml = shift;
  my $pws_xml = shift;
  my $description_of_corruption = shift;

  eval {
    VHTI::gen_comm::generate_commitment ($g_kgp_xml,
                                         snarf ("../examples/auth0.xml"),
                                         $bvs_xml,
                                         $pws_xml);
  };
  like ($@, $expected_exception_regexp, "proper exception from generate_commitment with $description_of_corruption");
}

sub gen_pub {
  my $expected_exception_regexp = shift;
  my $bvs_xml = shift;
  my $description_of_corruption = shift;

  eval {
    VHTI::gen_pubkey::generate_public_key ($g_kgp_xml,
                                           $bvs_xml);
  };
  like ($@, $expected_exception_regexp, "proper exception from generate_public_key with $description_of_corruption");
}

sub check_comm {
  my $expected_failure_regexp = shift;
  my $kgp_xml = shift;
  my $bvs_xml = shift;
  my $ksc_xml = shift;
  my $description_of_corruption = shift;
  my $result = VHTI::check_comm::check_commitment ($kgp_xml,
                                                   $g_auth_xml,
                                                   $bvs_xml,
                                                   $ksc_xml);

  like ($result, $expected_failure_regexp, "check_commitment noticed $description_of_corruption");
}

sub bogus_big_theta {
  my $bt = XML_Tree->construct ("BigTheta");
  $bt->add_attribute ("Order", "999");
  $bt->add_attribute ("Encoding", "DEC");
  $bt->add_characters ("1");
  $bt;
}

sub canonicalize_bvs {
  my $bvs_tree = shift;
  my $string;

  {
    my $big_thetas;
    foreach (grep { $_->name () eq "BigTheta" } @{$bvs_tree->elements ()}) {
      $big_thetas->{$_->attribute ("Order")} = $_;
    }
    foreach (sort (keys %$big_thetas)) {
      $string .= $big_thetas->{$_}->format_as_text ();
    }
  }

  $string .= $bvs_tree->e ("Omega")->format_as_text ();
  $string .= $bvs_tree->e ("Something")->format_as_text ();

  $string;
}

sub bvs_equal {
  canonicalize_bvs (XML_Tree->new (shift)) eq canonicalize_bvs (XML_Tree->new (shift));
}
