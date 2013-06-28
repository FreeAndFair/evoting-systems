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

my $project   = 'libvhti';
my $extension_cpp = '.cpp';
my $extension_h = '.h';

my $ofile = new IO::File;

%axtype = (
   STRING => "BSTR",
   INTEGER => "DWORD",
);

%param_prefix = (
   IN => '',
   OUT => '* ',
);

%arg_prefix = ( 
   IN => '', 
   OUT => '& ', 
);

%declare_t = (
   IN => { 
      STRING => sub { "_bstr_t $_[0]->{TNAME}($_[0]->{NAME})"; },
      INTEGER => sub { "int $_[0]->{TNAME} = $_[0]->{NAME}"; },
   },
   OUT => {
      STRING => sub { "const char * $_[0]->{TNAME} = NULL"; },
      INTEGER => sub { "int $_[0]->{TNAME} = 0"; },
   },
);

%finish_t = (
   STRING => sub { 
      "* $_[0]->{NAME} = _bstr_t($_[0]->{TNAME}).copy();\n"
      ."\t\tVHTI_free($_[0]->{TNAME})"; 
   },
   INTEGER => sub { "* $_[0]->{NAME} = $_[0]->{TNAME}"; },
);

# Write out the .h file.
open ($ofile, ">$root_path/$project$extension_h") || die "Unable to open output file $class_name$extension_h $!";

print $ofile <<"HFILE1";
/*============================================================================
$standard_header

$project$extension : $version : Declaration of the Clibvhti ole interface
============================================================================*/
#ifndef __LIBVHTI_H_
#define __LIBVHTI_H_

#include "resource.h"       // main symbols

/////////////////////////////////////////////////////////////////////////////
// Clibvhti
class ATL_NO_VTABLE Clibvhti : 
	public CComObjectRootEx<CComSingleThreadModel>,
	public CComCoClass<Clibvhti, &CLSID_libvhti>,
	public IDispatchImpl<Ilibvhti, &IID_Ilibvhti, &LIBID_VHTI_ACTIVEXLib>
{
public:
	Clibvhti()
	{
	}

DECLARE_REGISTRY_RESOURCEID(IDR_LIBVHTI)

DECLARE_PROTECT_FINAL_CONSTRUCT()

BEGIN_COM_MAP(Clibvhti)
	COM_INTERFACE_ENTRY(Ilibvhti)
	COM_INTERFACE_ENTRY(IDispatch)
END_COM_MAP()

// Ilibvhti
public:
HFILE1
   print $ofile map { 
      my $fn = $_; 
      "\tSTDMETHOD($fn->{SHORT})(".
      (
         join ', ', 
	      map({
                "/*[".lc($_->{DIR})."]*/ $axtype{$_->{TYPE}}"
                ." $param_prefix{$_->{DIR}}$_->{NAME}"
              } @{$fn->{ARGS}})
	      ,"/*[out,retval]*/ int * p_return"
      ).
      ");\n";
   } values %functions;
   print $ofile <<"HFILE2";
};

#endif //__LIBVHTI_H_

HFILE2
close $ofile;

#============================================================================#
# END OF HEADER OUTPUT
#============================================================================#

# Write out the vhti.cpp file.
open ($ofile, ">$root_path/$project$extension_cpp") || die "Unable to open output file $class_name$extension_cpp $!";

print $ofile <<"CPPFILE1";
/*============================================================================
$standard_header

$project$extension_cpp : $version : $description

$info
============================================================================*/
#include "stdafx.h"
#include "Vhti_activex.h"
#include "libvhti.h"

CPPFILE1

print $ofile ( join "\n",
             map { 
	       "#include \"vhti/$_\""
	     } &get_base_filenames(@include_files)
);
print $ofile <<"CPPFILE2";

/////////////////////////////////////////////////////////////////////////////
// Clibvhti
/////////////////////////////////////////////////////////////////////////////

CPPFILE2

   print $ofile map {
      my $fn = $_;
      # Function declaration
      ( 
         'STDMETHODIMP Clibvhti::'.$fn->{SHORT}.'('.
         join(', ', 
	    map({
              '/*['.lc($_->{DIR}).']*/ '
              .$axtype{$_->{TYPE}}
              .' '.$param_prefix{$_->{DIR}}
              .$_->{NAME}
           } @{$fn->{ARGS}}),
	   "/*[out,retval]*/ int * p_return"
	 ).
         ")\n{\n"
      ).
      # Var declarations and VHTI_ call w/result
      (
         join('', 
	      map { 
                "\t".$declare_t{$_->{DIR}}{$_->{TYPE}}($_).";\n" 
              } @{$fn->{ARGS}}
	 ).
         "\tDWORD ax_result = S_OK;\n".
         "\tint result = $fn->{NAME}(".
         join(', ', 
	       map { 
                 $arg_prefix{$_->{DIR}}.$_->{TNAME}; 
               } @{$fn->{ARGS}}
	 ).
	 ");\n"
      ).      
      # Condition checking on result and preping return values
      (
         "\tif (result)\n\t{\n\t\tax_result = E_FAIL;\n\t}\n\telse\n\t{\n".
         join('', 
	      map {
                "\t\t ".$finish_t{$_->{TYPE}}($_).";\n";
              } @{$fn->{OUT}}
	 ).
	 "\t}\n\n"
      ).
      "\t* p_return = result;\n".
      "\treturn ax_result;\n}\n\n";
   } values %functions;

close($ofile);

1;
