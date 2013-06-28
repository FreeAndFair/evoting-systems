#! /usr/bin/perl
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
#----------------------------------------------------------------------------# 
# Copyright 2003 VoteHere Inc. All Rights Reserved.
#
# First pass at a more generic generate_interface.pl type program.
#----------------------------------------------------------------------------# 
use FindBin qw ($RealBin);
use lib "$RealBin";
use mki::VHTI_Interface;
use Data::Dumper;
use Getopt::Long qw(:config gnu_compat);
use File::Path;

my @configs;
my @scripts;
my @func_files;
my $root_path;

my $help = q<
==============================================================================
mkinterface.pl -h | [-r root] -c config [...] [-s script [...]]
               [-r root] -f functions [...] -s script [...]
               [-r root] -c config [...] -f functions [...] [-s script [...]]

Options:
  -h                         |   This help info
  -f functions               |   Function file to read in
  -c config                  |   Config file to parse
  -s script                  |   Template script (perl)
  -r root                    |   Set a root output path for all output files

Simplified access with scripts to structures and data:
(Print Dumper(data_ref) to learn more about the actual structure from script.)

  Function hash:         %functions
  File array (unique):   @function_files
  Function list by file: %functions_by_files

  Default Copyright line:  $copyright_text
  Default header text:     $header_text
  Default standard header: $standard_header ( = $copyright_text\n$header_text)
  Version for this interface: $version

  Gen_Interface Object:    $generator
==============================================================================
>;

GetOptions(
  'config|c=s' => \@configs,
  'function|f=s'     => \@func_files,
  'help|h=s'   => sub { print $help; exit; },
  'root|r=s'   => \$root_path,
  'script|s=s' => \@scripts,
) || (print $help) && (exit);
if ((@configs < 1) && (@func_files < 1)) { print $help; exit; }

$y = new mki::VHTI_Interface;
if (defined $root_path) { 
  $y->root_path($root_path); 
}

$y->{verbose} = 0; # Turn on verbose mode.
$y->{debug} = 0;   # Turn on debug mode (more verbose).
$y->{version} = '0.0'; # Set a bogus version so everybody
                       # can tell when we didn't set it properly.

# Process each config file.
map { 
  $y->process_config_file($_);  
} @configs;

# We got our function files from the config
if ((@func_files < 1)) {
#  $y->generate_functions();
#  open(T,"> $RealBin/functions");
#  $y->dump_functions(*T);
#  close(T);
}
# We got our function files from cmdline
else {
  map { $ffile = $_; if ($ffile =~ /^*/) { $ffile = "functions"; } $y->read_functions($ffile); } @func_files;
}

map { $y->do_script($_); } @scripts;         # Run scripts passed by cmd
#map { $y->do_script($_); } @{$y->{scripts}}; # Run scripts found in config


# Ignore everything below this line.  Working on a procedural
# interface to the data structures, but not really 
# tested or used yet.
#print "<<".Dumper(function('VHTI_encrypt_ballot')).">>";
sub new_uuid {
  my ($uuid,$string);
  UUID::generate($uuid); 
  UUID::unparse($uuid,$string);
  return $string;
}

sub function($) { return $y->{functions}->{shift @_}; }
sub functions { return (keys %{$y->{functions}}); }
sub include_files() { return (@{$y->{function_files}}); }
sub file_functions($) { return (values %{$y->{functions_by_file}->{shift @_}}); }
sub function_arg($) { return $y->{functions}->{shift @_}->{ARGS}->[shift @_]; }
sub function_args($) { return @{$y->{functions}->{shift @_}->{ARGS}}; }
sub function_in($) { return $y->{functions}->{shift @_}->{IN}->[shift @_]; }
sub function_ins($) { return @{$y->{functions}->{shift @_}->{IN}}; }
sub function_out($) { return $y->{functions}->{shift @_}->{OUT}->[shift @_]; }
sub function_outs($) { return @{$y->{functions}->{shift @_}->{OUT}}; }
sub function_num_outs($) { return $#{$y->{functions}->{shift @_}->{OUT}}+1; }
sub function_name($) { return $y->{functions}->{shift @_}->{NAME}; }
sub function_file($) { return $y->{functions}->{shift @_}->{FILE}; }
sub function_short($) { return $y->{functions}->{shift @_}->{SHORT}; }
