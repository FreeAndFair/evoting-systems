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
unit demo_topform;

interface

uses
  Windows, Messages, SysUtils, Variants, Classes, Graphics, Controls, Forms,
  Dialogs, StdCtrls, Buttons, xmldom, XMLIntf, msxmldom, XMLDoc, demo_const;

type
  TTopForm = class(TForm)
    NewElection: TBitBtn;
    OpenElection: TBitBtn;
    procedure NewElectionClick(Sender: TObject);
    procedure OpenElectionClick(Sender: TObject);
  private
    { Private declarations }
  public
    { Public declarations }
    ElectionPath : string;
    NumAuth : integer;
    Threshold : integer;
    procedure UpdateState;
    procedure LoadElection(filepath : string);
    procedure SetElectionString(name : string; value : string);
    function GetElectionString(name : string) : string;
    function HasElectionString(name : string) : boolean;
    procedure RemoveElectionString(name : string);
    function FilenameForElectionString(name : string) : string;
  end;

procedure SetEnabledForShow(b : TButton; filename : string = '');
procedure SetCheckedForDone(b : TCheckBox; filename : string = '');

var
  TopForm: TTopForm;

implementation

uses
  new_election, open_election, election_phases, vh_support, vhti;

{$R *.dfm}

procedure SetEnabledForShow(b : TButton; filename : string = '');
begin
  if filename <> '' then
    b.Enabled := TopForm.HasElectionString(filename)
  else
    b.Enabled := TopForm.HasElectionString(b.Hint);
end;

procedure SetCheckedForDone(b : TCheckBox; filename : string = '');
begin
  if filename <> '' then
    b.Checked := topForm.HasElectionString(filename)
  else
    b.Checked := TopForm.HasElectionString(b.Hint);
end;

procedure TTopForm.UpdateState;
begin
  election_phases.ElectionPhasesForm.UpdateState;
end;

procedure TTopForm.LoadElection(filepath : string);
begin
  ElectionPath := filepath;
  Visible := false;
  ElectionPhasesForm.Visible := true;
end;

procedure TTopForm.SetElectionString(name : string; value : string);
begin
  vh_support.dump_file(FilenameForElectionString(name), value);
end;

function TTopForm.GetElectionString(name : string) : string;
begin
  GetElectionString := vh_support.suck_file(FilenameForElectionString(name));
end;

function TTopForm.HasElectionString(name : string) : boolean;
begin
  HasElectionString := FileExists(FilenameForElectionString(name));
end;

procedure TTopForm.RemoveElectionString(name : string);
begin
  DeleteFile(FilenameForElectionString(name));
end;

function TTopForm.FilenameForElectionString(name : string) : string;
begin
  FilenameForElectionString := ElectionPath + demo_const.path_sep + name
end;

procedure TTopForm.NewElectionClick(Sender: TObject);
begin
  NewElectionForm.Visible := true;
end;

procedure TTopForm.OpenElectionClick(Sender: TObject);
begin
  OpenElectionFrm.Visible := true;
end;

begin
  vhti.throw_exception_on_error := true;
end.
