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
use Carp;

require Exporter;
our @ISA = qw(Exporter);

our @EXPORT_OK = qw(unsnarf snarf update_stats);

sub unsnarf {
  my $text = shift;
  my $fn   = shift;

  # Make subdirectory if necessary.
  {
    my @path_components = split qr(/), $fn;
    pop @path_components;       # last component was the name of the
                                # actual file, not a directory
    foreach (@path_components) {
      if (! -d $_) {
        mkdir $_
          or croak "Can't create directory $_ because $!; stopped";
        warn "Created directory $_\n";
      }
    }
  }

  open (OUT, ">$fn")
    or croak "Can't open $fn for writing: $!; stopped";
  print OUT $text;
  close OUT;
  print STDERR "Wrote $fn\n";
}

sub snarf {
  my $fn = shift;

  open (IN, "<$fn")
    or croak "Can't open $fn for reading: $!; stopped";
  my $text = join ('', <IN>);
  close IN;
  $text;
}

sub update_stats {

  # Note the two different uses of `eval', distinguished by the types
  # of parentheses.

  my $stats = {};
  my $snarfed_text = eval { snarf ("stats") };

  if ($@) {
    warn "No `stats' file; creating a new one" ;
  } else {
    eval ($snarfed_text);
  }

  foreach my $func (keys %{$VHTI::perf_hash}) {
    foreach (keys %{$VHTI::perf_hash->{$func}}) {
      $stats->{$func}->{$_} += $VHTI::perf_hash->{$func}->{$_};
    }
  }
  unsnarf (Data::Dumper->Dump ([$stats], [qw(stats)]), "stats");
}
