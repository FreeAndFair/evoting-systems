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
#########################

use Test::More tests => 10;
use VHTI;
use VHTI::keyshare_util;
use VHTI::random;

#########################
use FindBin;
use lib "$FindBin::Bin";
use common;

my $random_state_xml = VHTI::random::generate_random_state (qq(<RandomSeedKey></RandomSeedKey>));
my $kgp_xml;

my $seed_parameters_tree = XML_Tree->construct ("SeedParameters");
$seed_parameters_tree->new_element ("NumAuth")->add_characters ("1");
$seed_parameters_tree->new_element ("Threshold")->add_characters ("2");

# A negative test: the function should fail because it doesn't
# make sense for the threshold to exceed the number of authorities.

eval {
  VHTI::keyshare_util::create_keygen_parameters
      ($seed_parameters_tree->format_as_text (),
       $random_state_xml);
};

like ($@, qr(THRESHOLD_EXCEEDS_NUMAUTH), "proper exception when threshold exceeds numauth");

my $num_auth = 3;
my $threshold = 2;
$seed_parameters_tree->e ("NumAuth")->remove_all_characters ();
$seed_parameters_tree->e ("NumAuth")->add_characters ($num_auth);
$seed_parameters_tree->e ("Threshold")->remove_all_characters ();
$seed_parameters_tree->e ("Threshold")->add_characters ($threshold);


($kgp_xml, $random_state_xml) = VHTI::keyshare_util::create_keygen_parameters ($seed_parameters_tree->format_as_text (),
                                                                               $random_state_xml);

use lib "$FindBin::Bin/../../../../toast/modules";
use XML_Tree;

# First we check some properties of the CryptoGroupParameters ...

my $cgp_tree = XML_Tree->new ($kgp_xml)->e ("CryptoGroupParameters");

my $election_modulus = $cgp_tree->e ("ElectionModulus"        )->characters (); # aka P
my $subgroup_modulus = $cgp_tree->e ("ElectionSubgroupModulus")->characters (); # aka Q
my $generator        = $cgp_tree->e ("ElectionSubgroupMember" )->characters (); # aka G

# Time to do some math.

use Math::Pari qw(:all :int); # Math::Pari is probably gross
                                # overkill, but what the hell.

# a PARI function to count bits, since I can't seem to figure out how
# to write a perl function to do the same thing
PARI ("pari_bits(x)=matsize(binary(x))[2]");

# This perl function just calls the PARI function ...
sub bits {
  # Bizarre, but true: if I say `$n = shift' here, I get a run-time
  # error: `Variable in perl2pari is not of known type at line 75.'
  PARI ("pari_bits($_[0])");
}

ok (isprime ($election_modulus), "Election modulus is prime.");
is (bits ($election_modulus), 1024, "Election modulus is the right length");
is (bits ($subgroup_modulus),  160, "Subgroup modulus is the right length");
ok (isprime ($subgroup_modulus), "Election subgroup order is prime.");
is ($subgroup_modulus, gcd ($election_modulus -  1, $subgroup_modulus), "Subgroup order divides modulus minus one.");
ok (Mod (PARI ($generator), $election_modulus) ** PARI ($subgroup_modulus) == Mod (1, $election_modulus), "generator really generates the subgroup." );

# the subgroup modulus is known as Q in our documentation.
my $r = ($election_modulus - 1) / $subgroup_modulus;
ok (($r % $subgroup_modulus) > 0, "r is not a multiple of q");

# Now look at the rest of the KeyGenParameters.

my $kgp_tree = XML_Tree->new ($kgp_xml);
cmp_ok ($kgp_tree->e ("NumAuth"  )->characters (), '==' , $num_auth , "NumAuth wasn't mangled");
cmp_ok ($kgp_tree->e ("Threshold")->characters (), '==' , $threshold, "Threshold wasn't mangled");
