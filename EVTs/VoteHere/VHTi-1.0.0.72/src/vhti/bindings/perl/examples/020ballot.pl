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
use constants;
use Getopt::Std;

my $cep_xml = snarf ("cep.xml");

use VHTI;
use VHTI::support;

use files;

use FindBin;
use lib "$FindBin::Bin/../../../../toast/modules";
use XML_Tree;

VHTI::set_error_mode('CROAK');

use VHTI::gen_blank_ballot;

our ($opt_q, $opt_a);

getopt ("qa");

my $bb_xml;
{
  my $ballot_skeleton_xml;
  if (!defined ($opt_q)
      &&
      !defined ($opt_a)) {
    eval {
      $ballot_skeleton_xml = snarf ("ballot-skeleton.xml");
      warn "Using existing ballot-skeleton.xml\n";
    };
    if ($@) {
      print "\nuse the -q and/or -a options to have a ballot skeleton generated automatically\n";
      die ($@);
    }
  } else {
    $opt_q = 4 unless defined ($opt_q);
    $opt_a = 3 unless defined ($opt_a);

    warn "Automatically generating ballot skeleton with $opt_q questions; $opt_a answers per question\n";
    {
      my $questions;

      for (my $answers = 0;
           $answers < $opt_a * $opt_q;
           $answers++) {
        use POSIX;
        my $qs = floor ($answers / $opt_a);
        $questions->{$qs}->{answers}->{$answers} = { text => "Answer $answers" };

        if (0 == ($answers % $opt_a)) {
          $questions->{$qs}->{title} = "Question $qs";
        }
      }

      my $ballot_skeleton_tree = XML_Tree->construct ("BallotSkeleton");
      $ballot_skeleton_tree->add_element (XML_Tree->construct ("ElectionID")->add_characters ("123"));
      $ballot_skeleton_tree->add_element (XML_Tree->construct ("PrecinctID")->add_characters ("87"));

      foreach my $qref (sort keys %$questions) {

        my $q_skel_tree = XML_Tree->construct ("QuestionSkeleton");

        $q_skel_tree->add_attribute ("QuestionReference", $qref);
        $q_skel_tree->new_element ("QuestionTextStructure")->add_characters ($questions->{$qref}->{title});

        my $answers = $questions->{$qref}->{answers};
        foreach my $answer_id (sort keys %$answers) {
          my $ballot_answer_tree = $q_skel_tree->new_element ("AnswerSkeleton");
          $ballot_answer_tree->add_attribute ("AnswerReference",

                                              # This is annoying --
                                              # one of the pollsite
                                              # tests looks for answer
                                              # ref `A0', so if we
                                              # accidentally omit the
                                              # `A' here, that test
                                              # fails.  It should
                                              # really be more robust.
                                              "A$answer_id"
                                             );
          $ballot_answer_tree->new_element ("AnswerTextStructure")->add_characters ($answers->{$answer_id}->{text});
        }
        $ballot_skeleton_tree->add_element ($q_skel_tree);
      }
      $ballot_skeleton_tree->add_element (XML_Tree->new ("<BallotTextStructure>THIS BALLOT SHOULD BE PLAYED LOUD</BallotTextStructure>"));
      $ballot_skeleton_xml = $ballot_skeleton_tree->format_as_text ();
    }
  }
  $bb_xml = VHTI::gen_blank_ballot::generate_blank_ballot ($ballot_skeleton_xml,
                                                           $cep_xml,
                                                           ALPHABET_ENCODING);
}
unsnarf ($bb_xml, "bb.xml");

# OK, now we gotta sign it.  To prepare for that, we gotta make us a
# key pair.

use VHTI::sign;
use VHTI::genkeys;
use POSIX;

my $ident_info = XML_Tree->construct ("IdentInfo");
$ident_info->add_characters ("$0 " . strftime (q(%Y-%m-%dT%XZ), gmtime (time)));
(my $private_key_xml, my $public_key_xml) = VHTI::genkeys::generate_keys ($ident_info->format_as_text ());

unsnarf (VHTI::sign::sign_xml ($private_key_xml, $bb_xml), "sbb.xml");
unsnarf ($private_key_xml, "pollsite-private-key.xml");
unsnarf ($public_key_xml , "pollsite-pubkey.xml");

update_stats ();
