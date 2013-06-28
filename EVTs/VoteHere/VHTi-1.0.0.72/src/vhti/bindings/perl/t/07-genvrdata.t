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
use Test::More tests => 5;

BEGIN { use_ok('VHTI') };
BEGIN { use_ok('VHTI::gen_vote_receipt_data') };

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

use VHTI::random;
my $random_state_xml = VHTI::random::generate_random_state (qq(<RandomSeedKey>Hamburgers!  The cornerstone of any nutritious breakfast.</RandomSeedKey>));

my $svb = snarf ("$FindBin::Bin/../examples/voter-Joe_Voter_#0/svb.xml");
my $vvks= snarf ("$FindBin::Bin/../examples/DRE/vvks.xml");
my $bb_tree = XML_Tree->new (snarf ("$FindBin::Bin/../examples/bb.xml"));

my $num_questions;
for ($num_questions = 0;
     $bb_tree->e ("BallotQuestion", $num_questions);
     $num_questions++) {
}

my $ctb_tree = XML_Tree->construct ("ClearTextBallot");
add_some_answer_refs ($ctb_tree, $num_questions - 1);
go ($bb_tree,
    qr(WRONG_NUMBER_OF_ANSWERS), "proper exception with too few answer refs");

add_some_answer_refs ($ctb_tree, 2);
go ($bb_tree,
    qr(WRONG_NUMBER_OF_ANSWERS), "proper exception with too many answer refs");

$ctb_tree = XML_Tree->construct ("ClearTextBallot");
add_some_answer_refs ($ctb_tree, $num_questions);
go (corrupted_blank_ballot ($bb_tree),
    qr(NOT_SUBGROUP_MEMBER), "detect answer marks that aren't members of the election subgroup");

sub go {
  my $bb_tree = shift;
  my $regexp = shift;
  my $message = shift;

  eval {
    my $receipt 
      = VHTI::gen_vote_receipt_data::generate_vote_receipt_data ($svb,
                                                                 $vvks,
                                                                 $bb_tree->format_as_text (),
                                                                 q(<BallotSequenceNumber Encoding="DEC">1</BallotSequenceNumber>),
                                                                 $ctb_tree->format_as_text (),
                                                                 VERIFICATION_CODE_BIT_LENGTH,
                                                                 ALPHABET_ENCODING);
    warn $receipt;
  };
  like ($@, $regexp, $message);
}

