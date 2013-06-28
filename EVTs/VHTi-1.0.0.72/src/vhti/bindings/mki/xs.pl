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

local $project   = 'VHTI_XS';
local $extension = '.xs';
local $description = "XS glue for Perl extension to VoteHere's VHTI API.";

local %arg_prefix = (
   IN => '',
   OUT => '& ',
);
local %output_newSV_fn = (
   STRING => sub { my $n = shift; "$n ? newSVpv($n, strlen($n)):&PL_sv_undef"; },
   INTEGER => sub { my $n = shift; "newSVnv($n)"; },
   );
local %output_cleanup_fn = (
   STRING => sub { my $n = shift; "VHTI_free((char *)$n);"; },
   INTEGER => sub { ''; },
   );

# Time to generate some output.  Start with the .xs file.
my $template = q+/* 

{= $standard_header =}

*/

// {= $project.$extension =} - {= $description =}

#include "EXTERN.h"
#include "perl.h"
#include "XSUB.h"

#include "ppport.h"

{= join '', map { "#include <vhti/$_>\n" } &get_base_filenames(@include_files); =}

MODULE = {=$project=}   PACKAGE = {=$project=} 

{=
join("\n", 
    map {
      local $fname = $_;
      local $fdes = $functions{$fname};
      do_template($func_template);
    } sort keys %functions );
=}
+;

local $func_template = q+
void
{=$fname=}({=join(", ", map { $_->{NAME} } @{$fdes->{IN} })=})
   {=join("\n   ",map { $_->{CTYPE}.' '.$_->{NAME}.";" } @{$fdes->{IN} })=}
   INIT:
     {=join("\n      ",map { $_->{RTYPE}.' '. $_->{NAME}." = NULL;" } @{$fdes->{OUT}})=}
     int res;
   PPCODE:
     res = {=$fname=}({=join(", ", map { $arg_prefix{$_->{DIR} } . $_->{NAME} } @{$fdes->{ARGS} })=});
     XPUSHs(sv_2mortal(newSVnv(res)));
     if (res == 0) {
       {=join("\n         ",map { 'XPUSHs(sv_2mortal('.(&{$output_newSV_fn{$_->{TYPE}}}($_->{NAME})).'));'; } @{$fdes->{OUT}})=}
     }
     {=join("\n     ",map { &{$output_cleanup_fn{$_->{TYPE} } }($_->{NAME}) } @{$fdes->{OUT} })=}
+;

out_script($project.$extension,$template);

1;
