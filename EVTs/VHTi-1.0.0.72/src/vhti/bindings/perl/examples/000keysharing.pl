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
use VHTI::keyshare_util;
use VHTI::random;
use VHTI::support;
use VHTI::gen_seccoeff;
use VHTI::gen_broadcast;
use VHTI::gen_pubkey;
use VHTI::gen_secrets;
use VHTI::gen_comm;
use VHTI::check_comm;

use files;
use constants;

use FindBin;
use lib "$FindBin::Bin/../../../../toast/modules";
use XML_Tree;

VHTI::set_error_mode('CROAK');

my $random_state_xml = VHTI::random::generate_random_state (qq(<RandomSeedKey/>));

my $kgp_tree;

eval {
  $kgp_tree = XML_Tree->new (snarf ("kgp.xml"));
  warn "Using existing kgp.xml\n";
};

if ($@) {

  my $seed_paramaters_tree = XML_Tree->construct ("SeedParameters");
  {
    my $num_auth = $seed_paramaters_tree->new_element ("NumAuth");
    $num_auth->add_characters ("4");
  }
  {
    my $thresh = $seed_paramaters_tree->new_element ("Threshold");
    $thresh->add_characters ("2");
  }
  (my $kgp_xml, $random_state_xml)
    = VHTI::keyshare_util::create_keygen_parameters ($seed_paramaters_tree->format_as_text (),
                                                     $random_state_xml);
  $kgp_tree = XML_Tree->new ($kgp_xml);
  unsnarf ($kgp_tree->format_as_text () . "\n", "kgp.xml");
}

unsnarf ($kgp_tree->e ("CryptoGroupParameters")->format_as_text (), "cgp.xml");

{
  use Math::Pari qw(isprime gcd PARI);

  # Sanity-check the numbers:

  # it seems the library ought to do these checks for me, but I don't
  # think it does.

  # These checks are copy-n-pasted from the perl bindings tests; of
  # course they ought to be factored out.

  my $election_modulus = PARI ($kgp_tree->e ("CryptoGroupParameters")->e ("ElectionModulus"        )->characters ());
  my $subgroup_modulus = PARI ($kgp_tree->e ("CryptoGroupParameters")->e ("ElectionSubgroupModulus")->characters ());
  my $generator        = PARI ($kgp_tree->e ("CryptoGroupParameters")->e ("ElectionSubgroupMember" )->characters ());

  die "inconsistency in test data: Election modulus $election_modulus is not prime."
    unless (isprime ($election_modulus));
  die "inconsistency in test data: Election subgroup order $subgroup_modulus is not prime."
    unless (isprime ($subgroup_modulus));
  die "inconsistency in test data: Subgroup order $subgroup_modulus does not divide modulus ($election_modulus) minus one."
    unless ($subgroup_modulus eq gcd ($election_modulus -  1, $subgroup_modulus));
  die "inconsistency in test data: so-called generator $generator doesn't generate the order-$subgroup_modulus subgroup."
    unless ("1" eq PARI ("Mod($generator,$election_modulus)^$subgroup_modulus==Mod(1,$election_modulus)"));
}

my $crypto_election_params_tree = XML_Tree->construct ("CryptoElectionParameters");
$crypto_election_params_tree->add_element ($kgp_tree->e ("CryptoGroupParameters"));
my $crypto_tab_params_tree = $crypto_election_params_tree->new_element ("CryptoTabulationParameters");

####################

# The keys of this hash will be the same as the relevant element names
# from our DTD.
my $auth_hash;


# Keep track of all the evalution points, so that we don't
# accidentally use the same one twice.  This is absurdly unlikely when
# the election modulus is large, but quite likely when it's small
# (e.g., during testing).

my $used_auth_evaluation_points;

for (my $i = 0;
     # Note that there is no "Encoding" attribute defined for NumAuth,
     # so it's correct to interpret the characters as a decimal
     # number.
     $i < $kgp_tree->e ("NumAuth")->characters ();
     $i++) {

  my $private_key;
  my $temp_authority;
  my $tries = 0;
  for (;
       $tries < 10;
       $tries++) {

    ($private_key, $temp_authority, $random_state_xml)
      = VHTI::keyshare_util::create_authority ($i, $kgp_tree->format_as_text (), $random_state_xml, "");

    my $evaluation_point = XML_Tree->new ($temp_authority)->e ("AuthorityEvaluationPoint")->characters ();

    if (!exists $used_auth_evaluation_points->{$evaluation_point}) {
      $auth_hash->{$i}->{Authority} = $temp_authority;
      $used_auth_evaluation_points->{$evaluation_point}++;
      last ;
    }
  }

  die "After $tries tries, couldn't find a unique authority evaluation point.\n"
    . "You might try using a different seed key, or fewer answers, or a bigger election subgroup.\n"
      if (!exists $auth_hash->{$i}->{Authority});

  # Writing out the public key like this is redundant, since it's
  # already present in both the authority and committed authority.
  # But it's convenient for some of the XML tests that are written in
  # C.
  unsnarf (XML_Tree->new($temp_authority)
           ->e ("Certificate")
           ->e ("GeneralPurposePublicKey")
           ->format_as_text (),
           "auth${i}-public-key.xml");

  unsnarf ("$private_key\n", "auth$i/private-key");

  ($auth_hash->{$i}->{SecretCoefficients}, $random_state_xml)
    = VHTI::gen_seccoeff::generate_secret_coefficients ($kgp_tree->format_as_text (),
                                                        $auth_hash->{$i}->{Authority},
                                                        $random_state_xml);
  ($auth_hash->{$i}->{BroadcastValue}, $random_state_xml)
    = VHTI::gen_broadcast::generate_broadcast ($kgp_tree->format_as_text (),
                                               $auth_hash->{$i}->{SecretCoefficients},
                                               $random_state_xml);
}

my $broadcast_values_xml;
{
  my $tree = XML_Tree->construct ("BroadcastValues");
  foreach (map { $_->{BroadcastValue} } values (%$auth_hash)) {
    $tree->add_element (XML_Tree->new ($_));
  }

  $broadcast_values_xml = $tree->format_as_text ();
}

unsnarf ($broadcast_values_xml, "broadcast-values.xml");

$crypto_tab_params_tree->add_element (XML_Tree->new (VHTI::gen_pubkey::generate_public_key ($kgp_tree->format_as_text (),
                                                                                            $broadcast_values_xml)));

$crypto_tab_params_tree->add_element ($kgp_tree->e("NumAuth"));
$crypto_tab_params_tree->add_element ($kgp_tree->e("Threshold"));

for (my $recipients = 0;
     $recipients < $kgp_tree->e ("NumAuth")->characters ();
     $recipients++) {
  for (my $senders = 0;
       $senders < $kgp_tree->e ("NumAuth")->characters ();
       $senders++) {
    $auth_hash->{$recipients}->{PairwiseSecretsFrom}->{$senders}
      = VHTI::gen_secrets::generate_secret ($kgp_tree->format_as_text (),
                                            $auth_hash->{$recipients}->{Authority},
                                            $auth_hash->{$senders}->{SecretCoefficients});
  }

  my $pws;
  {
    my $tree = XML_Tree->construct ("PairwiseSecrets");
    foreach (values (%{$auth_hash->{$recipients}->{PairwiseSecretsFrom}})) {
      $tree->add_element (XML_Tree->new ($_));
    }
    $pws = $tree->format_as_text ();
  }

  ($auth_hash->{$recipients}->{SecretShare},
   $auth_hash->{$recipients}->{KeyShareCommitment})
    = VHTI::gen_comm::generate_commitment ($kgp_tree->format_as_text (),
                                           $auth_hash->{$recipients}->{Authority},
                                           $broadcast_values_xml,
                                           $pws);

  $auth_hash->{$recipients}->{VerificationResults}
    = VHTI::check_comm::check_commitment ($kgp_tree->format_as_text (),
                                          $auth_hash->{$recipients}->{Authority},
                                          $broadcast_values_xml,
                                          $auth_hash->{$recipients}->{KeyShareCommitment});

  $crypto_tab_params_tree->add_element (XML_Tree->new ($auth_hash->{$recipients}->{KeyShareCommitment}));

  my $committed_authority_tree = XML_Tree->construct ("CommittedAuthority");

  $committed_authority_tree->add_element (XML_Tree->new ($auth_hash->{$recipients}->{Authority}));
  $committed_authority_tree->add_element (XML_Tree->new ($auth_hash->{$recipients}->{KeyShareCommitment}));

  # TODO -- should I name these files after $recipients, or something
  # else -- such as the authority evaluation point, or the ident info
  # in the certificate?

  # TODO -- double check these, and make sure that everything that
  # should be kept secret is indeed in our subdirectory.  Getting this
  # wrong won't break anything, but it'd be nice.

  unsnarf ($pws,
           "auth${recipients}/pws.xml");
  unsnarf ($auth_hash->{$recipients}->{KeyShareCommitment},
           "auth${recipients}-ksc.xml");
  unsnarf ($auth_hash->{$recipients}->{Authority},
           "auth${recipients}.xml");
  unsnarf ($auth_hash->{$recipients}->{SecretCoefficients},
           "auth${recipients}/secret-coefficients.xml");
  unsnarf ($auth_hash->{$recipients}->{SecretShare},
           "auth${recipients}/secret-share.xml");
  unsnarf ($committed_authority_tree->format_as_text () . "\n",
           "committed-auth-${recipients}.xml");
}

unsnarf ($crypto_election_params_tree->format_as_text () . "\n", "cep.xml");

update_stats ();
