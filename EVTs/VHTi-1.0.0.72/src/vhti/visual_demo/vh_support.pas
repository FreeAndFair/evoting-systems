(*  *)
(* This material is subject to the VoteHere Source Code Evaluation *)
(* License Agreement ("Agreement").  Possession and/or use of this *)
(* material indicates your acceptance of this Agreement in its entirety. *)
(* Copies of the Agreement may be found at www.votehere.net. *)
(*  *)
(* Copyright 2004 VoteHere, Inc.  All Rights Reserved *)
(*  *)
(* You may not download this Software if you are located in any country *)
(* (or are a national of a country) subject to a general U.S. or *)
(* U.N. embargo or are deemed to be a terrorist country (i.e., Cuba, *)
(* Iran, Iraq, Libya, North Korea, Sudan and Syria) by the United States *)
(* (each a "Prohibited Country") or are otherwise denied export *)
(* privileges from the United States or Canada ("Denied Person"). *)
(* Further, you may not transfer or re-export the Software to any such *)
(* country or Denied Person without a license or authorization from the *)
(* U.S. government.  By downloading the Software, you represent and *)
(* warrant that you are not a Denied Person, are not located in or a *)
(* national of a Prohibited Country, and will not export or re-export to *)
(* any Prohibited Country or Denied Party. *)
unit vh_support;

interface

uses
  windows;

function suck_file(filename : string) : string;
procedure dump_file(filename, contents : string);
procedure launch_file(handle : HWND; filename : string);
function make_random_string(len : integer) : string;

implementation

uses
  SysUtils, dialogs, shellapi, xmlintf;

function suck_file;
var
  f : text;
  ch : char;
  contents : string;
begin
  AssignFile(f, filename);
  Reset(f);
  while not EOF(f) do
  begin
    Read(f, ch);
    contents := contents + ch;
  end;
  CloseFile(f);
  suck_file := contents;
end;

procedure dump_file;
var
  f : text;
begin
  AssignFile(f, filename);
  Rewrite(f);
  Write(f, contents);
  CloseFile(f);
end;

procedure launch_file(handle : HWND; filename : string);
var
  fullpath : string;
  command : string;
  startupInfo : TStartupInfo;
  processInfo : TProcessInformation;
  Result : boolean;
begin
  fullpath := SysUtils.GetCurrentDir + '\' + filename;
  command := 'iexplore.exe "' + fullpath + '"';
  command := 'c:\foo.xml';
  command := filename;
  ShellAPI.ShellExecute(handle, 'Open', PChar(command), nil, nil, SW_SHOW);
{  ShowMessage('Unable to start process, error code = '
      + IntToStr(GetLastError));  }
  ShellAPI.ShellExecute(handle, 'Open', PChar(fullpath), nil, nil, SW_SHOW);

{
  (* Initialize the startupInfo. *)
  FillChar(startupInfo, sizeof(startupInfo), 0);
  startupInfo.cb := sizeof(startupInfo);
  GetStartupInfo(startupInfo);

  Result := Windows.CreateProcess(nil,  // application name
      PChar(command),  // command line
      nil,  // process attributes
      nil,  // thread attributes
      false,  // inherit handles
      CREATE_DEFAULT_ERROR_MODE or NORMAL_PRIORITY_CLASS,  // flags
      nil,  // environment
      nil,  // current directory
      startupInfo,  // startup info
      processInfo);  // process information
  if not Result then
    ShowMessage('Unable to start process, error code = '
        + IntToStr(GetLastError))
  else with processInfo do
  begin
    CloseHandle(hProcess);
    CloseHandle(hThread);
  end;
}
end;

function make_random_string(len : integer) : string;
var
  resultString : string;
  i : integer;
begin
  resultString := '';
  for i := 1 to len do
  begin
    resultString := resultString + chr(random(26) + ord('a'));
  end;
  make_random_string := resultString;
end;

end.

