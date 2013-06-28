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

local $project   = 'VHTI';
local $extension = '.pm';
local $description = "Perl extension for VoteHere's voting API.";

#============================================================================#
# Write out the VHTI.pm file.
#============================================================================#

local $vhti_load_type = q+
our $INTERFACE_HINT = $ENV{VHTI_INTERFACE_HINT};
our $VHTI_INCLUDE = $ENV{VHTI_INCLUDE_PATH} || '.';
our $vhti_lib;
BEGIN {
  local $INTERFACE_HINT = $ENV{VHTI_INTERFACE_HINT};
  local $VHTI_INCLUDE = $ENV{VHTI_INCLUDE_PATH} || dirname(__FILE__);

  if (! defined $INTERFACE_HINT) { $INTERFACE_HINT = $^O; }
  SWITCH: {
    $INTERFACE_HINT =~ /OLE/io && do {
      $vhti_lib = "VHTI_OLE"; last SWITCH;
    };
    $INTERFACE_HINT =~ /MSWIN/io && do {
      $vhti_lib = "VHTI_XS"; last SWITCH;
    };
    $INTERFACE_HINT =~ /CYGWIN/io && do {
      $vhti_lib = "VHTI_XS"; last SWITCH;
    };
    die "No interface for VHTI for your platform $INTERFACE_HINT.\n\n".
    "You could try setting $VHTI::INTERFACE_HINT='CYGWIN'\n".
    "before calling \"use VHTI;\"  This will use the xs glue.\n";
  }
  if (defined $VHTI_INCLUDE) { 
    $vhti_lib = "$VHTI_INCLUDE/$vhti_lib";
  }
}
use lib "$vhti_lib";
use VHTI_Extend; #.pm";
our @ISA = qw( VHTI_Extend Exporter );
+;

do "mki/vhti_pm_core.pl";
out_script($project.$extension,$vhti_core_pm);

1;
