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
package pki_common;

use Data::Dumper;
use Test::More;
use common;
use VHTI::crypt;
use VHTI::sign;

require Exporter;
our @ISA = qw(Exporter);

our @EXPORT = qw(good_keypair_10_tests corrupt_element corrupt_string);

sub good_keypair_10_tests {
  my $prv = shift;
  my $pub = shift;

  my $plaintext = qq(
<snurkly foo = "bar">
Hi.  I'm a snurkly.
</snurkly>
Hello World 2.
This plaintext is rather long, isn't it?
In fact, it's more than 128 bytes long.
Now, 128 is a magic number, in that that's the longest byte-sequence that RSA encryption can handle.
Thus if VHTI_encrypt is stupidly passing the plaintext directly to RSA, it'll bungle this, and return -1
(and you might see "data too large for key size" in the diagnostics).
But if it's wisely generating a random 128-byte session key, encrypting that, and then using that as the key for
a symmetric cipher (as God intended), then all will be well.);

  encryption_tests ($prv, $pub, $plaintext);
  signing_tests    ($prv, $pub, $plaintext);

  # Make sure it works with XML that isn't already canonicalized.  Extra
  # whitepace around the `=' sign counts as not canonicalized.
  $plaintext = q(<duh><zippy yow     =     "Am I CONSING yet?"/></duh>);

  encryption_tests ($prv, $pub, $plaintext);
  signing_tests    ($prv, $pub, $plaintext);
}

sub encryption_tests {
  my $prv = shift;
  my $pub = shift;
  my $plaintext = shift;

  my $encrypted   = VHTI::crypt::encrypt($pub, $plaintext);
  my $unencrypted = VHTI::crypt::decrypt($prv, $encrypted);

  is($unencrypted, $plaintext, 'encrypted document matches plaintext');
  {
    my $corrupt_tree = XML_Tree->new ($encrypted);
    corrupt_element ($corrupt_tree, "CipherText");

    eval {
      VHTI::crypt::decrypt ($prv, $corrupt_tree->format_as_text ());
    };
    ok ($@, "detects corrupted ciphertext");
  }

  {
    my $corrupt_private_key = XML_Tree->new ($prv);
    corrupt_element ($corrupt_private_key, "EncryptionPrivateKey");
    eval {
      VHTI::crypt::decrypt ($corrupt_private_key->format_as_text (), $encrypted);
    };
    ok ($@, "detects corrupted private key");
  }
}

sub signing_tests {
  my $prv = shift;
  my $pub = shift;
  my $tbs = shift;

  my $signature = VHTI::sign::sign  ($prv, $tbs);
  my $v_res     = VHTI::sign::verify_signature ($pub, $tbs, $signature);

  like ($v_res, qr{(Success)}, 'verify_signature signature success');
  {
    my $corrupt_tbs = corrupt_string ($tbs);
    $v_res = VHTI::sign::verify_signature ($pub, $corrupt_tbs, $signature);
    like ($v_res, qr{(Failure)}, "detects corrupted to-be-signed");
  }

  {
    my $corrupt_sig = corrupt_string (XML_Tree->new ($signature)->characters ());
    eval {
      VHTI::sign::verify_signature ($pub, $tbs, "<Signature>$corrupt_sig</Signature>");
      };
    ok ($@, "detects corrupted signature");
  }
}

sub corrupt_string {
  my $victim = shift;
  my @corrupted = split (qr(), $victim);
  my $middle_character = @corrupted[scalar (@corrupted) / 2];
  if ('?' eq $middle_character) {
    $middle_character = '!';
  } else {
    $middle_character = '?';
  }
  @corrupted[scalar (@corrupted) / 2] = $middle_character;
  my $corrupted = join ('', @corrupted);

  $corrupted;
}

sub corrupt_element {
  my $elt = (elt_by_path (@_));

  my $corrupted_characters = corrupt_string ($elt->characters ());
  $elt->remove_all_characters ();
  $elt->add_characters ($corrupted_characters);
}
