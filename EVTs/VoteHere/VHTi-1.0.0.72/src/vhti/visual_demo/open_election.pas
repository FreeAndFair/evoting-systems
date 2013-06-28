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
unit open_election;

interface

uses
  Windows, Messages, SysUtils, Variants, Classes, Graphics, Controls, Forms,
  Dialogs, StdCtrls, FileCtrl;

type
  TOpenElectionFrm = class(TForm)
    ParentDirectory: TDirectoryListBox;
    OkButton: TButton;
    CancelButton: TButton;
    Label2: TLabel;
    ParentDrive: TDriveComboBox;
    procedure ParentDriveChange(Sender: TObject);
    procedure CancelButtonClick(Sender: TObject);
    procedure OkButtonClick(Sender: TObject);
  private
    { Private declarations }
  public
    { Public declarations }
  end;

var
  OpenElectionFrm: TOpenElectionFrm;

implementation

uses
  demo_topform, vh_support, demo_const, election_phases;

{$R *.dfm}

procedure TOpenElectionFrm.ParentDriveChange(Sender: TObject);
begin
  ParentDirectory.Drive := ParentDrive.Drive;
end;

procedure TOpenElectionFrm.CancelButtonClick(Sender: TObject);
begin
  Visible := false;
end;

procedure TOpenElectionFrm.OkButtonClick(Sender: TObject);
var
  name : string;
  filepath : string;
  contents : string;
  goal : string;
begin
  name := ParentDirectory.Directory;
  filepath := name + path_sep + demo_const.election_config;
  contents := vh_support.suck_file(filepath);
  goal := demo_const.xml_element(election_config, '', '');
  if contents <> goal then
  begin
    ShowMessage('This does not appear to be a valid election.')
  end
  else
  begin
    TopForm.ElectionPath := name;
    TopForm.Visible := false;
    TopForm.NumAuth := StrToInt(TopForm.GetElectionString(demo_const.num_auth));
    TopForm.Threshold := StrToInt(TopForm.GetElectionString(demo_const.threshold));
    ElectionPhasesForm.UpdateState;
    ElectionPhasesForm.Visible := true;
  end;
  Visible := false;
end;

end.
