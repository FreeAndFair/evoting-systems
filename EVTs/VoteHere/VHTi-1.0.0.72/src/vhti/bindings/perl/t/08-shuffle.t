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
use Test::More tests => 6;

BEGIN { use_ok('VHTI') };
BEGIN { use_ok('VHTI::random') };
BEGIN { use_ok('VHTI::gen_blank_ballot') };
BEGIN { use_ok('VHTI::genkeys') };
BEGIN { use_ok('VHTI::sign') };
BEGIN { use_ok('VHTI::shuffle') };

use FindBin;
use lib ("$FindBin::Bin", "$FindBin::Bin/../examples");
use common;
use lib "$FindBin::Bin/../../../../toast/modules";
use XML_Tree;
use POSIX;
use files;
use constants;
use pscommon;

use warnings;
use strict;
use Data::Dumper;

chdir ("$FindBin::Bin")
  or die "Can't cd to $FindBin::Bin: $!; stopped";

my $random_state_xml = VHTI::random::generate_random_state (qq(<RandomSeedKey></RandomSeedKey>));
my $empty_rbb_xml = XML_Tree->construct ("RawBallotBox")->format_as_text ();
my $ballot_skeleton_xml = snarf ("../examples/ballot-skeleton.xml");
my $cep_xml = snarf ("../examples/cep.xml");
my $bb_xml = VHTI::gen_blank_ballot::generate_blank_ballot ($ballot_skeleton_xml,
                                                            $cep_xml,
                                                            ALPHABET_ENCODING);
my $ident_info = XML_Tree->construct ("IdentInfo");
$ident_info->add_characters ("$0 " . strftime (q(%Y-%m-%dT%XZ), gmtime (time)));
(my $private_key_xml, my $public_key_xml) = VHTI::genkeys::generate_keys ($ident_info->format_as_text ());
my $sbb_xml = VHTI::sign::sign_xml ($private_key_xml, $bb_xml);

# We're simply ensuring we don't get an exception when shuffling empty
# ballot box.
VHTI::shuffle::shuffle ($empty_rbb_xml,
                        $random_state_xml,
                        $sbb_xml,
                        $public_key_xml);
