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
use Test::More tests => 23;
BEGIN { use_ok('VHTI') };
BEGIN { use_ok('VHTI::support') };
BEGIN { use_ok('VHTI::genkeys') };
BEGIN { use_ok('VHTI::sign') };

use FindBin;
use lib "$FindBin::Bin";
use common;
use lib "$FindBin::Bin/../../../../toast/modules";
use XML_Tree;
use POSIX;
use pki_common;

my $io = XML_Tree->construct ("IdentInfo");
$io->add_characters ("$0 " . strftime (q(%Y-%m-%dT%XZ), gmtime (time)));

(my $prv, my $pub) = VHTI::genkeys::generate_keys($io->format_as_text ());
ok (good_keypair_10_tests ($prv, $pub), 'generate keys');

my $xml_tbs = "<AnswerReference>Normally, `AnswerReference' is some number or other.  But we'll just use text.</AnswerReference>";
my $signed_xml = VHTI::sign::sign_xml ($prv, $xml_tbs);

my $signed_tree = XML_Tree->new ($signed_xml);
my $signed_data = $signed_tree->e ("SignedData");
my $signature   = $signed_tree->e ("Signature");

# Make sure the older signature-verification code likes it ...
$v_res = VHTI::sign::verify_signature($pub, $signed_data->characters (), $signature->format_as_text ());
like($v_res, qr{(Success)}, 'signed XML signature verifies');

# Likewise with the new spiffy signed-XML-signature-verification code.
($v_res, my $inner_xml) = VHTI::sign::check_xml ($pub, $signed_xml, "AnswerReference");
like($v_res, qr{(Success)}, 'signed XML signature checks');
is ($inner_xml, $xml_tbs, "unwrapped XML matches what we originally signed");

{
  my $corrupted_tree = XML_Tree->construct ("SignedAnswerReference");
  $corrupted_tree->add_element (XML_Tree->construct ("SignedData")->add_characters (corrupt_string ($signed_xml)));
  $corrupted_tree->add_element ($signature);

  ($v_res, my $inner_xml) = VHTI::sign::check_xml ($pub, $corrupted_tree->format_as_text (), "AnswerReference");
  like ($v_res, qr(Failure), "detect corrupted plaintext");
  unlike ($inner_xml, qr(^<), "Correctly returned non-XML when sig failed to check");

  # Once again, only this time corrupt the signature, not the to-be-signed text
  $corrupted_tree = XML_Tree->construct ("SignedAnswerReference");
  $corrupted_tree->add_element (XML_Tree->construct ("SignedData")->add_characters ($signed_xml));
  $corrupted_tree->add_element (XML_Tree->construct ("Signature")->add_characters (corrupt_string ($signature->characters ())));

  eval {
    VHTI::sign::check_xml ($pub, $corrupted_tree->format_as_text (), "AnswerReference");
  };
  ok ($@, "detects corrupted signature");
}
