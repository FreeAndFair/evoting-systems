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

use Math::BigInt lib => 'Pari,GMP';
use Data::Dumper;

use Test::More tests => 3;

use VHTI;
use VHTI::random;

use FindBin;
use lib "$FindBin::Bin";
use common;
use lib "$FindBin::Bin/../../../../toast/modules";
use XML_Tree;

#warn "Using " . Math::BigInt->config()->{lib};

sub log2 {
  my $bignum = Math::BigInt->new (shift);
  length ($bignum->as_bin()) - 2;
}

my $random_bits_xml;
my $bits_requested = 32000;     # smaller quantities tend to yield
                                # lower entropy per byte

my $random_state_xml = VHTI::random::generate_random_state (qq(<RandomSeedKey></RandomSeedKey>));
($random_state_xml, $random_bits_xml)  = VHTI::random::get_bits ($random_state_xml, $bits_requested);

if (0) {
  diag "This test is disabled because it's mighty slow.  Edit this file ($0) in the obvious way to activate it.";
  pass ("");
  pass ("");
} else {

  my $big_random_number = xml_2_bignum ($random_bits_xml);

  use File::Temp qw(tempfile);

  my $entropy_bits_per_byte;
  my @bytes;
  while (!$big_random_number->is_zero()) {
    unshift @bytes, ($big_random_number % 256)->bstr ();
    $big_random_number->bdiv (256);
  }

  {
    (my $fh, my $filename) = tempfile (UNLINK => 1);

    print $fh pack ("C*", @bytes);
    close ($fh);

    $ENV{PATH} .= ":/usr/local/bin";

    open (ENT, "-|", "ent", "-t", $filename) || die "Can't fork: $!";
    while (<ENT>) {
      next unless ($. == 2);    # skip first line
      $entropy_bits_per_byte = (split qr(,))[2];
      last;
    }

    close ENT || die "Ent failed: $! $?";
  }

  ok ($entropy_bits_per_byte > 7.5, "At least 7.5 bits of entropy per output byte.");

  # Now make sure we're getting back as many bits as we requested.  I
  # can think of no absolutely certain way to test this, since if we ask
  # for a million bits, the code might legitimately return a million
  # zeroes (i.e., zero), yet we'd have no way of knowing that it was
  # doing the right thing.  So we simply assume that that's unlikely
  # (which of course it is).  We'll ask for n random bits, and check
  # that returned value has at least n - 40 bits.  This test will give a
  # false negative on average one time in every 2 ** 40 runs, which is
  # rarely enough for me.

  use constant {
    DESIRED_BITS => 2007
  };

  my $too_many = 0;
  my $not_enough = 0;

  foreach (1 .. 3) {
    ($random_state_xml, $random_bits_xml)  = VHTI::random::get_bits ($random_state_xml, DESIRED_BITS);

    $big_random_number = xml_2_bignum ($random_bits_xml);
    my $bits_gotten = log2 ($big_random_number);

    unless ($bits_gotten >= (DESIRED_BITS - 40)) {
      $not_enough = 1;
      last;
    }
    unless ($bits_gotten <= (DESIRED_BITS)) {
      $too_many = 1;
      last;
    }
  }

  ok (!$not_enough, "got enough bits");
  ok (!$too_many  , "not too many bits");
}
