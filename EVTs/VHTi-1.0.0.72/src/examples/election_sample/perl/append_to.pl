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

$fn_in = '';
$fn_out = '';

$fn_in = shift @ARGV;
$fn_out = shift @ARGV;
$name = shift @ARGV;
die "Usage: append_to.pl IN_XML OUT_XML XML_ELEMENT_NAME" unless defined $fn_in && $fn_out && $name;

my $in_tree = XML_Tree->new (snarf ("$fn_in"));
my $out_tree;
eval {
   $out_tree = XML_Tree->new (snarf ("$fn_out"));
};

# Output file doesn't exist yet
if ($@) {
   $out_tree = XML_Tree->construct ($name);
}

$out_tree->add_element ($in_tree);
unsnarf ($out_tree->internal_format_as_text () . "\n", $fn_out);
