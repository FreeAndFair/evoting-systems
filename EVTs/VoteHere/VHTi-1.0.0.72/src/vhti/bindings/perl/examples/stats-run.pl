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

# TODO -- come up with some whizzy scheme whereby we take the output
# of this script, and from it generate a graph for each combination of
# VHTI function and knob (e.g., we'd see VHTI_encrypt_ballot_pollsite
# : trustees; VHTI_encrypt_ballot_pollsite : voters;
# VHTI_encrypt_ballot_pollsite: questions;
# VHTI_encrypt_ballot_pollsite: answers).  Each such graph would of
# course have the knob settings as the X axis, and time as the Y axis.
# Thus anyone could, at a glance, see if any function is responding in
# a surprising way (i.e., we expect it to be linear but it's
# quadratic, or whatever).  The GNU Plotutils seem a reasonable choice
# for generating the graphs.

# The script `one-func.pl' in this directory is a start.

warn "Make sure that VHTI is not doing all its modular exponentations twice!  Check support/support_internal.h.\n";

my %knobs = ( trustees => [1, 2 , 5, 6 ],
              voters   => [1, 2, 10, 11, 30, 31, 100, 101 ],
              questions=> [1 , 2, 10, 11, 30, 31 ],
              answers  => [1, 2, 10, 11, 30, 31 ],
            );

my $trustees  = 0;
my $voters    = 0;
my $questions = 0;
my $answers   = 0;

$ENV{PATH} = "$ENV{PATH}:.";

# Do one run with each knob at its lowest setting.
set_them_all_to_lowest ();
one_run ();

# Now, for each knob that has more than one setting, and for each of
# those other settings, do a run with that knob at that setting, and
# all the other knobs at their lowest setting.

foreach my $name (keys %knobs) {
  next unless scalar ($knobs{$name}) > 1;

  my @settings = @{$knobs{$name}};

  foreach (@settings[1 .. $#settings]) {

    set_them_all_to_lowest ();

    eval ('$' . "$name = $_");

    one_run ();
  }
}

sub set_them_all_to_lowest {
  foreach my $name (keys %knobs) {
    eval ('$' . "$name = $knobs{$name}[0]");
  }
}

sub one_run {
  my $stuff = { parameters => {questions => $questions,
                               answers => $answers,
                               voters => $voters,
                               trustees => $trustees}};

  system ("clean.sh");

  system ("rm -f stats");

  system ("./go.sh 000keysharing.pl");
  system ("./go.sh 010trustees.pl -t $trustees");
  system ("./go.sh 020ballot.pl   -q $questions -a $answers");
  system ("./go.sh 030vote.pl     -v $voters ");
  system ("./go.sh 040tabulate.pl  ");

  {
    my $stats;
    eval (qx (cat stats));
    $stuff->{stats} = $stats;
  }

  my $fn = "stats-" . qx(date --utc +%Y-%m-%dT%H-%M-%SZ);
  chomp $fn;
  open (COMPLETE_RUN, ">", $fn)
    or die "Can't open $fn for writing: $!; stopped";
  print COMPLETE_RUN Dumper ($stuff) ;
  close (COMPLETE_RUN);
}
