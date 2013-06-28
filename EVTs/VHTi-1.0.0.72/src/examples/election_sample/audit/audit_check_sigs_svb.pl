#!/usr/bin/perl -w
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

use files;
use XML_Tree;
use VHTI;
use VHTI::sign;

$fn_pubkey = shift @ARGV;
$fn_svb = shift @ARGV;
$fn_return = shift @ARGV;
die "Usage: audit_check_sigs_svb.pl PUBLIC_KEY SVB_FILE RESULT_FILE" unless defined $fn_pubkey && $fn_svb && $fn_return;

my $pubkey = snarf ($fn_pubkey);
my $svbs_tree = XML_Tree->new (snarf ($fn_svb));

my $cb = 1;
foreach my $svb_tree (grep {$_->name () eq "SignedVotedBallot"} @{$svbs_tree->elements ()}) {
   (my $sig_check_result, my $svb_xml) = VHTI::sign::check_xml ($pubkey,
                                                                $svb_tree->internal_format_as_text (),
                                                                "VotedBallot");

   if (XML_Tree->new ($sig_check_result)->characters () !~ qr(0:Success)) {
      $error = "<CheckResults>FAILED: SignedVotedBallot $cb signature</CheckResults>";
      unsnarf ($error, $fn_return);
      exit;
   }
   print "SignedVotedBallot $cb signature ... checked.\n";
   $cb++;
}

$error = "<CheckResults>0:Success</CheckResults>";
unsnarf ($error, $fn_return);
