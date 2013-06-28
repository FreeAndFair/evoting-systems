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

package common;

use warnings;
use strict;
use Carp;
use Math::BigInt lib => 'GMP';

require Exporter;
our @ISA = qw(Exporter);

our @EXPORT = qw(xml_2_bignum corrupted_blank_ballot elt_by_path);

VHTI::set_error_mode('CROAK');

sub xml_2_bignum
{
  my $tree = XML_Tree->new (shift);
  my $encoding = $tree->attribute ("Encoding");
  if ("DEC" eq $encoding) {
    return new Math::BigInt ($tree->characters ());
  } elsif ("BASE64" eq $encoding) {

    # this is certainly roundabout (and slow), but I can't think
    # of a more straightforward way to do it.

    use MIME::Base64;
    my $binary_data = decode_base64($tree->characters ());

    return new Math::BigInt ("0x" . unpack ("H*", $binary_data));
  } else {
    die "Unrecognized encoding: $encoding";
  }
}

sub corrupted_blank_ballot {
  my $bb_tree = XML_Tree->new (shift->format_as_text ());
  # Corrupt the blank ballot by replacing the first answer mark with a value that isn't a member of the election subgroup.

  my $first_answer_mark = elt_by_path ($bb_tree, "BallotQuestion", "BallotAnswer", "AnswerMark");
  $first_answer_mark->remove_all_characters ();
  $first_answer_mark->add_characters (non_member ($bb_tree));
  $bb_tree;
}

sub non_member {

  # find an element which isn't a member of the subgroup.  There might
  # be a clever way to do this, but since I can't think of one, I'll
  # simply pick elements of the larger group at random until I stumble
  # onto one.  Since the larger group typically has 2^1024 elements
  # whereas the subgroup typically has 2^160 elements, this shouldn't
  # take long.

  my $bb_tree = shift;
  my $random_big_group_element = 0;
  my $election_modulus = elt_by_path ($bb_tree, "CryptoElectionParameters", "CryptoGroupParameters", "ElectionModulus")->characters ();
  my $subgroup_order   = elt_by_path ($bb_tree, "CryptoElectionParameters", "CryptoGroupParameters", "ElectionSubgroupModulus")->characters ();

  while ((0 == $random_big_group_element)
         ||
         is_subgroup_member ($random_big_group_element, $election_modulus, $subgroup_order)) {
    use Math::Pari qw(random);
    $random_big_group_element = random ($election_modulus);
  }

  $random_big_group_element;
}

# Check if the number is a member of the subgroup by raising it to the subgroup
# order.  If and only if it is a member, the result will be one.

sub is_subgroup_member {
  use Math::Pari qw(Mod PARI);

  my $testee = PARI (shift);
  my $prime_modulus  = PARI (shift);
  my $subgroup_order = PARI (shift);

  my $result = Mod ($testee, $prime_modulus) ** $subgroup_order == Mod (1, $prime_modulus);

  $result;
}

sub elt_by_path {
  my $elt = shift;
  while (@_) {
    $elt = $elt->e (shift);
  }
  $elt;
}

1;
