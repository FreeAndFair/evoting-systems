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
die qq( 
  This is not a standalone script.  Please run it using 
  mkinterface.pl or your own wrapper around 
  VHTI_INTERFACE.pm
) if (! defined $generator_loaded_flag);

$vhti_core_pm = q[ 
package VHTI;

=head1 Notice
{= $standard_header =}
=cut
use strict;
use warnings;
use Carp;
use File::Basename;
use Data::Dumper;

our $VERSION = '{=$version=}';
{= 
$vhti_load_type 
=}
our %EXPORT_TAGS = ( 'all' => [ qw(
      raise_error
      available_error_modes
      set_error_mode
      set_custom_error_handler
      perf_sorted_stats
      perf_hash
      set_dump_key
      clear_dump_keys
      clear_dump_key
      set_dump_handler
) ] );

our @EXPORT_OK = ( @{ $EXPORT_TAGS{'all'} } );

our %DUMP_HASH;
our $PROFILE = 0;
our $perf_hash;
our $ERROR_MODE = 'UNDEF';
our $CUSTOM_ERROR_HANDLER = sub { return (@_); undef; };
our $DUMP_HANDLER = *dump_params;

our %AVAILABLE_ERROR_MODES = ( 
	'UNDEF'   => sub { return undef; }, 
	'NOISY'   => *Carp::carp,
	'CARP'    => *Carp::carp,
	'CLUCK'   => *Carp::cluck,
	'CROAK'   => *Carp::croak,
        'CONFESS' => *Carp::confess,	
	'CUSTOM'  => *CUSTOM_ERROR_HANDLER,
);

sub perf_hash { 
  return $perf_hash;
}

sub perf_sorted_stats {
  my @stats;
  foreach (keys %{$perf_hash}) {
    push @stats, ({name => $_ , $perf_hash->{$_}});
  }
  [sort { $a->{seconds} <=> $b->{seconds}} @stats];
}

sub set_profile_flag {
  if (0 == $_[0]) { $PROFILE = 0; }
  else { $PROFILE = 1; }
}

sub set_dump_key {
  my $key = shift || return;
  $DUMP_HASH{$key} = 1;
}

sub clear_dump_key {
  my $key = shift;
  if (defined $key) {
    delete $DUMP_HASH{$key};
  }
  else {
    %DUMP_HASH = undef;
  }
}

sub set_dump_handler {
   $DUMP_HANDLER = shift || *dump_params;
}

sub dump_params {
   my $fn = shift;
   my $res = shift;
   my $params = shift;
   #print Dumper($params);
   map {
     my $dir = $_;
     map { print "\t$fn [$dir] $_ $params->{$dir}->{$_}\n"; } sort keys %{$params->{$dir}};
   } ( 'IN','OUT');
   print "$fn (RESULT = $res)\n";
}

sub available_error_modes {
   sort keys %AVAILABLE_ERROR_MODES;
}

sub set_error_mode {
   $ERROR_MODE = shift;
}

sub set_custom_error_handler {
   $CUSTOM_ERROR_HANDLER = shift;
   $ERROR_MODE = 'CUSTOM';
}

1;

#__END__ 

=head1 NAME

{= $project =} - {= $description =}

=head1 SYNOPSIS

  use VHTI;

  The VHTI module does very little itself.  You will want to also
  include the needed packages VHTI::(package) that you need to
  use in your script.

=head1 DESCRIPTION

=head2 Methods

  set_profile_flag([0|1])
    
    Turns on(1) or off(0) the performance stats, which are kept in 
    $VHTI::perf_hash (ref).

  perf_hash()

    Returns the reference to the $VHTI::perf_hash.

  perf_sorted_stats()
   
    Returns sorted performance stats from $VHTI::perf_hash.

  raise_error(message)
  
    Sends an error to the handler specified with set_error_mode().

    Returns undef, unless a custom handler has been specified, which
    will return what the author defineds in the custom code.

  available_error_modes()

    Returns a list of error modes to send to set_error_mode().

  set_error_mode(mode_name)

    Sets the error handler to be used by name, which are provided
    by available_error_modes().

  set_custom_error_handler(code_ref)

    If 'CUSTOM' has been selected with set_error_mode(), you then
    need to provide the code reference that will be called at
    raise_error().  

    Custom handlers are passed the following parameters:
        {CODE}(function_return_value,function_name,message)

    raise_error() will propogates whatever the custom handler returns
    as its return value as well.

  set_dump_key(function_name|'all')
    
    When a VHTI function runs, if the function's name is in the dump
    hash, then all input and output parameters will be dumped to
    $VHTI::DUMP_HANDLER{CODE}.

  clear_dump_key([key])

    Either remove a key from the $VHTI::DUMP_HASH hash or if no
    parameters are passed, sets the hash to undef.
    
  set_dump_handler([code_ref])
    
    If a code reference has been passed, then all functions with
    their names in the %VHTI::DUMP_HASH will send their input
    and output parameters to your custom dump function.
    
    Parameters will be sent as a hash ref, with keys 'RESULT','IN',
    and 'OUT', which correspond to the parameter direction of the
    VHTI call and the value in RESULT the return value of the call.
    
    Each of the top keys point to a ref array of ref arrays, which
    has 3 elements, function name (0), data type (1), and data (2).
    
    Otherwise, $VHTI::DUMP_HANDLER{CODE} will be set to the default
    dump function which dumps the parameter values to STDOUT in a 
    simple format.
     
=head2 VHTI Public Packages

    The following packages were generated for this extension from
    the public functions of the VHTI library.

{= join "\n",
    map {
      my $file = $_ =~ /(?:.*?\/)*(.*)?\.h/;
      my $package = $1;       
      #$package =~ s/VHTI_/VHTI::/; 
      "    VHTI::".$package; 
    } sort @function_files
=}

=head2 EXPORT

  None by default.

=head1 SEE ALSO

  Documentation for VHTI lives in a document normally called vhapidoc.pdf,
  which is the source document for the public functions extended by this
  module.

  Look for it.

=head1 COPYRIGHT AND LICENSE

  {= $copyright_notice =}

=cut

];

1;
