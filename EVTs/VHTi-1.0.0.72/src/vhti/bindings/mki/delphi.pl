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

my $project   = 'vhti';
my $extension = '.pas';

use Data::Dumper;

#no_vhti_free();
no_vhti_dup();

open (FILE, ">$root_path/$project$extension") || croak "Unable to open $project$extension $!";
select FILE;

print <<"UNIT";
unit vhti;

(**************************************************************************
$standard_header
**************************************************************************)

interface

uses
  SysUtils;

type
  EVHTiError = class(Exception);

const
  VHTI_success = 0;

var
  throw_exception_on_error : boolean;  (* Defaults to false. *)

UNIT

%in_out_map = ('IN' => '', 'OUT' => 'var ');
%type_map = (
   'STRING' => 'string',
   'INTEGER' => 'integer');

for my $fn_name (sort keys %functions) {
   my $fn_info = $functions{$fn_name};
   my $fn_decl1 = "function $fn_info->{SHORT} (";
   my $fn_decl2 = ") : integer;\n\n";
   my $spaces = length($fn_decl1);
   if ($spaces > 50) {
      $spaces = 6;
      $fn_decl1 .= "\n" . ' ' x $spaces;
      $fn_decl2 = "\n    " . $fn_decl2;
   }
   print $fn_decl1 . join(";\n" . ' ' x $spaces, map {
         $in_out_map{$_->{DIR}} . $_->{NAME} . ' : ' . $type_map{$_->{TYPE}};
      } @{$fn_info->{ARGS}}) . $fn_decl2;
}

print <<'IMPL';

(*************************************************************************)
(*************************************************************************)

implementation

const
{$IFDEF MSWINDOWS}
  vhti_dll = 'vhti_dll.dll';
  (* vhti_dll = 'd:\home\brunch\development\vhti_internal\src\vhti_dll\debug\vhti_dll.dll'; *)
{$ENDIF}
{$IFDEF LINUX}
{$IFDEF WINE}
  vhti_dll = 'libvhti_dll.votehere.so';
{$ELSE}
  vhti_dll = 'libvhti_dll.so';
{$ENDIF}
{$ENDIF}

(*************************************************************************)

function internal_VHTI_free(p_thing : pchar) : integer;
  {$IFDEF WIN32} cdecl; {$ENDIF}
  external vhti_dll name 'VHTI_free';

function VHTI_free(p_thing : pchar) : integer;
  {$IFDEF WIN32} cdecl; {$ENDIF}
  forward;

(*************************************************************************)

procedure maybe_throw_exception(error_code : integer);
var
  err_string : string;
begin
  if throw_exception_on_error and (error_code <> 0) then
  begin
    throw_exception_on_error := false;
    (* Wouldn't want to make a recursive error situation here: *)
    get_last_error(err_string);
    throw_exception_on_error := true;
    raise EVHTiError.Create(err_string);
  end;
end;

IMPL

#type
#pinteger = ^ integer;   
#ppchar = ^ pchar;  (* Strictly not necessary, but to be clear. *)

%raw_type_map = (
   'STRING' => 'pchar',
   'INTEGER' => 'integer');

for my $fn_name (sort keys %functions) {
   my $fn_info = $functions{$fn_name};
   my $fn_decl1 = "function $fn_name (";
   my $fn_decl2 = ") : integer;\n";
   my $spaces = length($fn_decl1);
   if ($spaces > 50) {
      $spaces = 6;
      $fn_decl1 .= "\n" . ' ' x $spaces;
      $fn_decl2 = "\n    " . $fn_decl2;
   }
   print "(" . "*" x 73 . ")\n\n";
   print $fn_decl1 . join(";\n" . ' ' x $spaces, map {
	 $in_out_map{$_->{DIR}} . $_->{NAME} 
	 . ' : ' . $raw_type_map{$_->{TYPE}};
      } @{$fn_info->{ARGS}}) . $fn_decl2;
   print "  {\$IFDEF WIN32} cdecl; {\$ENDIF}\n"
   . "  external vhti_dll name '$fn_name';\n\n";

   print join("\n", 
      "function $fn_info->{SHORT};",
      '  var', 
      '    retval : integer;',
      (map { 
	    "    $_->{TNAME} : $raw_type_map{$_->{TYPE}};";
	 } @{$fn_info->{ARGS}}), 
      "  begin",
      (map {
	    "    $_->{TNAME} := $raw_type_map{$_->{TYPE}}($_->{NAME});"
	 } @{$fn_info->{IN}}),
      "    retval := $fn_name(" . join(", ", 
	 map { $_->{TNAME} } @{$fn_info->{ARGS}}) . ");", 
      "    if retval = 0 then begin",
      (map {
	    my $free = (($_->{TYPE} eq 'STRING') 
	       ? ("\n      VHTI_free($_->{TNAME});") : (''));
	    "      $_->{NAME} := $_->{TNAME};" . $free
	 } @{$fn_info->{OUT}}),
      '    end;',
      '    maybe_throw_exception(retval);',
      "    $fn_info->{SHORT} := retval;", 
      "  end;\n\n");
}

print <<"FINAL";

begin
  throw_exception_on_error := false;
end.

FINAL

select STDOUT;
close FILE;

