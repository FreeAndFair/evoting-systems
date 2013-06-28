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

local $project   = 'VHTI_Extend';
local $extension = '.pm';
local $description = "Perl XS extension for VoteHere's voting API.";
my $ext_dir = "VHTI_XS";
my $mod_dir = $ext_dir."/VHTI";

#=============================================================================#
# BEGIN OUTPUT TEMPLATE
#=============================================================================#
my $template = q(
package VHTI_Extend; # XS FLAVOR

=head1 NOTICE

{= $standard_header =}

=cut

use 5.008;
use strict;
use warnings;

our $VERSION = $VHTI::VERSION; 
$VHTI::INTERFACE_TYPE = 'XS';

#----------------------------------------------------------------------------#
# Interface specifics
#----------------------------------------------------------------------------#
use XSLoader;
XSLoader::load('VHTI_XS'); 
#----------------------------------------------------------------------------#

*VHTI::raise_error = *raise_error;

sub raise_error {
   my $res = shift;
   my $fn = shift;
   my $msg = shift || undef;

   my ($eres,$message);

   if (! defined $msg) {
     ($eres, $msg) = VHTI_XS::VHTI_get_last_error();   
     if ($eres) {
       # Grr, couldn't get error text.
       $message = "Unkown raise error $res in call to $fn.\n";
     } else {
        $message = "VHTI error $res : '$msg' in call to $fn.\n";
     }
   }
   else {
     $message = $msg;
   }

   if ($VHTI::ERROR_MODE eq 'CUSTOM') {
     return $VHTI::AVAILABLE_ERROR_MODES{$VHTI::ERROR_MODE}($res,$fn,$message);
   }
   $VHTI::AVAILABLE_ERROR_MODES{$VHTI::ERROR_MODE}($message);
   return undef;
}

1;

#__END__

=head1 NAME

{= $project =} - {= $description =}

=head1 SYNOPSIS

  This package handles specifics to a particular VHTI perl interface and
  is not to be called directly. VHTI.pm will select an appropriate module.

=over  

  use VHTI;

=back

=head1 DESCRIPTION

  This variation is a simple wrapper for package that provides 
  extensions to the C++ VHTI public API.

  VHTI exports "raw" VHTI_* functions.

=head2 EXPORT

  None by default to *main.

  Everything in this module is however exported to *VHTI namespace.

=head1 SEE ALSO

=over
=item * VHTI.pm

=item * Documentation for VHTI lives in a document normally called F<vhapidoc.pdf>. Look for this.

=item * The F<VHTI::*> packages are also implemented here.  Their interface is the same as that of the native perl bindings.
=back

=head1 COPYRIGHT AND LICENSE

{= $copyright_notice =}

=cut

);
#=============================================================================#
# END OUTPUT TEMPLATE
#=============================================================================#

out_script("$ext_dir/$project$extension",$template);

#=============================================================================#
# GENERATE TEMPLATES FOR ALL HEADER FILES
#=============================================================================#
map {
   /(?:.*?\/)*(.*)?\.h/;
   local $file = $_;
   local $filename = $1.".pm";
   local $module = $1;
   local $func_list = '';

#=============================================================================#
# BEGIN OUTPUT TEMPLATE
#=============================================================================#
     $template = q+
package VHTI::{= $module =};

=head1 NOTICE 

{= $standard_header =}
=cut

use Carp;

*raise_error = *VHTI::raise_error;

{=
join "\n",map {
  local $fn = $functions{$_};
  if ($fn->{NAME} eq 'VHTI_get_last_error_number') {
    q(
#-----------------------------------------------------------------------------#
sub get_last_error_number {
  return VHTI_XS::VHTI_get_last_error_number()
}
#-----------------------------------------------------------------------------#
    );
  }
  else {      
      do_template($function_template) ;	
  }
} sort @{ $functions_by_file{$file} };
=}

#__END__

=head1 NAME

VHTI::{=$module=} - Ole interface to VHTI_{=$module=} functions

=head1 SYNOPSIS

  use VHTI::{=$module=};

=head1 DESCRIPTION

  {= join "\n  ",
    map { 
      local $fn = $functions{$_};
      "VHTI::$module"."::$fn->{SHORT}(\n    ". 
      (
        join ",\n    ",
             map { "$_->{DIR} *$_->{RTYPE} $_->{NAME}" } @{$fn->{ARGS} }
      ).
      "\n  )"
    } sort @{ $functions_by_file{$file} };
=}

=head2 EXPORT

  None by default.

=head1 SEE ALSO

  Documentation for VHTI lives in a document normally called vhapidoc.pdf.
  Look for this.

=head1 COPYRIGHT AND LICENSE

{= $copyright_notice =}

=cut

+;
#=============================================================================#
# END OUTPUT TEMPLATE
#=============================================================================#

#=============================================================================#
# BEGIN FUNCTION OUTPUT TEMPLATE
#=============================================================================#
local $function_template = q[
sub {= $fn->{SHORT} =} {

  my $start_time = undef;  # When VHTI::PROFILE == 1, set this for benchmark

{= 
   join("\n",map {
"  # VHTI Input = *$_->{RTYPE} $_->{NAME}\n".
"  my \$".$_->{NAME}." = shift;\n".
"     &raise_error(-1,'$fn->{SHORT}','$_->{NAME} is a required parameter') if (! defined \$$_->{NAME});";
   } @{$fn->{IN}});
=}

  if (1 == $VHTI::PROFILE) { $start_time = HiRes::time(); } 
  my ({=join(',','$res',map { '$'.$_->{NAME} } @{ $fn->{OUT} } ) =}) = 
	  VHTI_XS::{= $fn->{NAME} =}(
              {= join( ",\n              ", 
	        map {'$'.$_->{NAME} } @{ $fn->{IN} })
              =}
          );
  if (defined $start_time) {
    $VHTI::perf_hash->{$rawfnname}->{seconds} += HiRes::time() - $start_time;
    $VHTI::perf_hash->{$rawfnname}->{calls}++;
  }

  if ((exists $VHTI::DUMP_HASH{'all'}) or (exists $VHTI::DUMP_HASH{'{= $fn->{SHORT} =}'})) {
    &$VHTI::DUMP_HANDLER( 
       '{= $fn->{SHORT} =}',
       $res, 
       {
       IN => {
           {= join(",\n           ",map { "$_->{NAME} => ".'$'.$_->{NAME} } @{ $fn->{IN} }) =}
       },
       OUT => {
           {= join(",\n           ",map { "$_->{NAME} => ".'$'.$_->{NAME} } @{ $fn->{OUT} }) =}
       },
       }
    );
  }
 
  unless (0 == $res) {
    &raise_error($res,'{=$fn->{SHORT}=}');
  }

  return ({= join(', ', 
                 map {'$'.$_->{NAME} } @{ $fn->{OUT} } 
	     );
         =});
}

];
#=============================================================================#
# END FUNCTION OUTPUT TEMPLATE
#=============================================================================#
  out_script("$mod_dir/$filename",$template);
} sort @function_files;

local $project   = 'VHTI_XS';
local $extension = '.pm';
local $description = "Perl2exe XS extension for VoteHere's voting API.";
local $vhti_load_type = q[
use VHTI_XS::VHTI_Extend; 
];
do "mki/vhti_pm_core.pl";
out_script("$ext_dir/$project$extension",$vhti_core_pm);

1;
