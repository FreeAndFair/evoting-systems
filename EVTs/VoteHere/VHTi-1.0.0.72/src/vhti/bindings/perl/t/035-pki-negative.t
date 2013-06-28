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
use Test::More tests => 8;

BEGIN { use_ok('VHTI') };
BEGIN { use_ok('VHTI::genkeys') };
BEGIN { use_ok('VHTI::sign') };

use FindBin;
use lib "$FindBin::Bin";
use common;
use lib "$FindBin::Bin/../../../../toast/modules";
use XML_Tree;
use POSIX;

use warnings;
use strict;
use Data::Dumper;

# Negative tests.

# check

# check_xml

# decrypt

# encrypt

# generate_keys: hard to see how this could be forced to fail

# sign: pass XML-valid, but still bogus, private key.
my $ident_info = q(<IdentInfo>I am some identification info.</IdentInfo>);
diag "Generating two key pairs; sorry about the wait.";
(my $prv1, my $pub1) = VHTI::genkeys::generate_keys($ident_info);
ok($prv1 && $pub1, 'generate keys first time');
(my $prv2, my $pub2) = VHTI::genkeys::generate_keys($ident_info);
ok($prv2 && $pub2, 'generate keys second time');

my $plaintext = "I am some plaintext.";
my $signature_1 = VHTI::sign::sign($prv1, $plaintext);

{
  my $bogus_prv = XML_Tree->new ($prv1);
  $bogus_prv->e ("SigningPrivateKey")->remove_all_characters ();
  $bogus_prv->e ("SigningPrivateKey")->add_characters ("I sure as hell ain't no signing private key.");

  eval {
    VHTI::sign::sign($bogus_prv->format_as_text (), $plaintext);
  };
}

like ($@, qr(DSA_KEY_PARSING_ERROR), "Proper exception from signing with bogus private key.");

# Similarly try to verify the signature with a bogus public key.
{
  my $bogus_pub = XML_Tree->new ($pub1);
  $bogus_pub->e ("SigningPublicKey")->remove_all_characters ();
  $bogus_pub->e ("SigningPublicKey")->add_characters ("I sure as hell ain't no signing public key.");

  eval {
    VHTI::sign::verify_signature($bogus_pub->format_as_text (), $plaintext, $signature_1);
  };
}

like ($@, qr(DSA_KEY_PARSING_ERROR), "Proper exception when verifying signature with bogus public key.");

# check a sig but pass in the wrong key.  This isn't strictly speaking
# a negative test, and is probably also checked elsewhere, but what
# the heck.

my $check_result = VHTI::sign::verify_signature($pub2, $plaintext, $signature_1);

like ($check_result, qr(Failure), "Proper failure when checking signature with wrong public key.");

# sign_xml
