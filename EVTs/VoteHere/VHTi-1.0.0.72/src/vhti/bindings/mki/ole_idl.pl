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
use IO::File;

die qq( 
  This is not a standalone script.  Please run it using 
  mkinterface.pl or your own wrapper around 
  VHTI_INTERFACE.pm
) if (! defined $generator_loaded_flag);

my $project   = 'vhti_activex';
my $extension = '.idl';

my $idl = new IO::File;

my @uuid = map {
  uc(new_uuid());
} 0..2;

my %axtype = (
   STRING => "BSTR",
   INTEGER => "DWORD",
);

my %param_prefix = (
   IN => '',
   OUT => '* ',
);

#-----------------------------------------------------------------------------
# Write out the .idl file.
#-----------------------------------------------------------------------------
$idl->open(">$root_path/$project$extension") 
  || die "Unable to open output file $project$extension $!";

print $idl <<"IDL1";
/*============================================================================
$standard_header

$project$extension : $version : IDL source for VHTI library

This file will be processed by the MIDL tool to produce the type library 
(vhti_activex.tlb) and marshalling code.
============================================================================*/
import "oaidl.idl";
import "ocidl.idl";
	[
		object,
		uuid($uuid[0]),
		dual,
		helpstring("Ilibvhti Interface"),
		pointer_default(unique)
	]
	interface Ilibvhti : IDispatch
	{
IDL1

my $idl_version = make_version(1,'.');

my $idno = 1;
print $idl map { 
  my $fn = $_; 
    "\t\t[id(@{[$idno ++]}), helpstring(\"method $fn->{SHORT}\")] HRESULT $fn->{SHORT}(".
    (
      join( ', ', map ({ 
                    "[".lc($_->{DIR})."] $axtype{$_->{TYPE}}"
                    ." $param_prefix{$_->{DIR}}$_->{NAME}"
                  } @{$fn->{ARGS}}), "[out,retval] int * p_return"
      )
    ).");\n";
} values %functions;

print $idl <<"IDL2";
	};

[
	uuid($uuid[1]),
	version($idl_version),
	helpstring("vhti_activex $version Type Library")
]
library VHTI_ACTIVEXLib
{
	importlib("stdole32.tlb");
	importlib("stdole2.tlb");

	[
		uuid($uuid[2]),
		helpstring("libvhti Class")
	]
	coclass libvhti
	{
		[default] interface Ilibvhti;
	};
};

IDL2
$idl->close;

#-----------------------------------------------------------------------------
# Write out the .idl file.
#-----------------------------------------------------------------------------
$project   = 'libvhti';
$extension = '.rgs';

$idl->open(">$root_path/$project$extension") 
  || die "Unable to open output file $project$extension $!";

print $idl <<"RGS";
/*============================================================================
$standard_header

$project$extension : $version : RGS Source VHTI OLE extension 
============================================================================*/
HKCR
{
	Vhti_activex.libvhti.1 = s 'libvhti Class'
	{
		CLSID = s '{$uuid[1]}'
	}
	Vhti_activex.libvhti = s 'libvhti Class'
	{
		CLSID = s '{$uuid[1]}'
		CurVer = s 'Vhti_activex.libvhti.1'
	}
	NoRemove CLSID
	{
		ForceRemove {$uuid[1]} = s 'libvhti Class'
		{
			ProgID = s 'Vhti_activex.libvhti.1'
			VersionIndependentProgID = s 'Vhti_activex.libvhti'
			ForceRemove 'Programmable'
			InprocServer32 = s '%MODULE%'
			{
				val ThreadingModel = s 'Apartment'
			}
			'TypeLib' = s '{$uuid[2]}'
		}
	}
}
RGS
$idl->close();

1;
