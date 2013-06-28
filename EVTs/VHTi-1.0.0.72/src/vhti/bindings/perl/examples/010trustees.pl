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

use files;

use FindBin;
use lib "$FindBin::Bin/../../../../toast/modules";
use XML_Tree;

VHTI::set_error_mode('CROAK');

use VHTI;
use VHTI::random;
use VHTI::gen_vvkey;
use VHTI::genkeys;

my $random_state_xml = VHTI::random::generate_random_state (qq(<RandomSeedKey/>));

my $vote_verify_keys = XML_Tree->construct ("VoteVerificationKeys");

our ($opt_t);

getopt ("t");

$opt_t = 3 unless defined ($opt_t);

warn "$opt_t trustees\n";

for (my $trustees = 0;
     $trustees < $opt_t;
     $trustees++) {
  (my $key, $random_state_xml) = VHTI::gen_vvkey::generate_vvk ($random_state_xml);
  $vote_verify_keys->add_element (XML_Tree->new ($key));

  unsnarf ($key, "trustee-$trustees/vvk.xml");
  (my $private_key_xml, my $public_key_xml) =  VHTI::genkeys::generate_keys (XML_Tree->construct ("IdentInfo")
                                                                             ->add_characters ("Vote Verification Trustee #$trustees")
                                                                             ->format_as_text ());
  unsnarf ($private_key_xml, "trustee-$trustees/private-key");
  unsnarf ($public_key_xml , "trustee-$trustees-pubkey.xml");
}

# This, as with many things, is redundant but convenient.  It goes
# into a subdirectory to imply that it's secret data.

unsnarf ($vote_verify_keys->format_as_text (), "DRE/vvks.xml");
update_stats ();
