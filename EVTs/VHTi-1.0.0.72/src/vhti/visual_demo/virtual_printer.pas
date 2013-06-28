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
unit virtual_printer;

interface

uses
  Windows, Messages, SysUtils, Variants, Classes, Graphics, Controls, Forms,
  Dialogs, StdCtrls;

type
  TPrinterOutput = class(TForm)
    VisibleText: TMemo;
    procedure FormResize(Sender: TObject);
  private
    { Private declarations }
  public
    { Public declarations }
    procedure PrintLine(line : string);
    procedure PrintMore(chars : string);
    procedure Tab(column : integer);
  end;

var
  PrinterOutput: TPrinterOutput;

implementation

{$R *.dfm}

uses
  strutils;

procedure TPrinterOutput.PrintLine(line : string);
begin
  VisibleText.Lines.Append(line);
end;

procedure TPrinterOutput.PrintMore(chars : string);
var
  line : string;
begin
  line := VisibleText.Lines.Strings[VisibleText.Lines.Count - 1];
  line := line + chars;
  VisibleText.Lines.Strings[VisibleText.Lines.Count - 1] := line;
end;

procedure TPrinterOutput.Tab(column : integer);
var
  line : string;
begin
  line := VisibleText.Lines.Strings[VisibleText.Lines.Count - 1];
  line := LeftStr(line, column);
  while Length(line) < column do
    line := line + ' ';
  VisibleText.Lines.Strings[VisibleText.Lines.Count - 1] := line;
end;

procedure TPrinterOutput.FormResize(Sender: TObject);
begin
  VisibleText.Width := ClientWidth;
  VisibleText.Height := ClientHeight;
end;

end.
