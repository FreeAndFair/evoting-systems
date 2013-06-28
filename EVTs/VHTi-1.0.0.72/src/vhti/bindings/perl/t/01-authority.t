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

use Test::More tests => 16;

use warnings;
use strict;
use Data::Dumper;

use VHTI;
use VHTI::keyshare_util;
use VHTI::random;

use FindBin;
use lib "$FindBin::Bin";
use common;
use pki_common;
use lib "$FindBin::Bin/../../../../toast/modules";
use XML_Tree;

my $kgp_tree = XML_Tree->construct ("KeyGenParameters");
{
  my $cgp = $kgp_tree->new_element ("CryptoGroupParameters");
  my $em = $cgp->new_element ("ElectionModulus");
  $em->add_attribute ("Encoding", "DEC");
  $em->add_characters ("47");
  my $esgm = $cgp->new_element ("ElectionSubgroupModulus");
  $esgm->add_attribute ("Encoding", "DEC");
  $esgm->add_characters ("23");
  my $esgg = $cgp->new_element ("ElectionSubgroupMember");
  $esgg->add_attribute ("Encoding", "DEC");
  $esgg->add_characters ("17");
  $kgp_tree->new_element ("NumAuth")->add_characters ("4");
  $kgp_tree->new_element ("Threshold")->add_characters ("2");
}

my $random_state_xml = VHTI::random::generate_random_state (qq(<RandomSeedKey/>));
(my $private_key, my $authority, $random_state_xml)
  = VHTI::keyshare_util::create_authority (qq(10),
                                           $kgp_tree->format_as_text (),
                                           $random_state_xml, "");

my $auth_tree = XML_Tree->new ($authority);
is ($auth_tree->attribute ("AuthFingerprint"), 10, "Correct fingerprint");
good_keypair_10_tests ($private_key, $auth_tree->e ("Certificate")->e ("GeneralPurposePublicKey")->format_as_text ());

my $evaluation_point = $auth_tree->e ("AuthorityEvaluationPoint")->characters ();

use Math::Pari qw(:all :int);

my $subgroup_modulus = $kgp_tree->e ("CryptoGroupParameters")->e ("ElectionSubgroupModulus");
ok ($evaluation_point < $subgroup_modulus->characters ());
ok ($evaluation_point > 0);

# make a bogus bignum, see if anybody notices
$subgroup_modulus->remove_all_characters ();
$subgroup_modulus->add_characters ("I Am Not a Number! I Am a Free man!");
eval {
  VHTI::keyshare_util::create_authority (qq(10),
                                         $kgp_tree->format_as_text (),
                                         $random_state_xml, "")
};
like ($@, qr(BADLY_FORMED_NUMBER), "notices bogus bignum");
