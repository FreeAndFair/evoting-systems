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
unit new_election;

interface

uses
  Windows, Messages, SysUtils, Variants, Classes, Graphics, Controls, Forms,
  Dialogs, StdCtrls, FileCtrl;

type
  TNewElectionForm = class(TForm)
    ParentDirectory: TDirectoryListBox;
    ElectionName: TEdit;
    OkButton: TButton;
    CancelButton: TButton;
    Label1: TLabel;
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
  NewElectionForm: TNewElectionForm;

implementation

uses
  demo_topform, vh_support, demo_const, election_phases, vhti;
  
{$R *.dfm}

procedure TNewElectionForm.ParentDriveChange(Sender: TObject);
begin
  ParentDirectory.Drive := ParentDrive.Drive;
end;

procedure TNewElectionForm.CancelButtonClick(Sender: TObject);
begin
  Visible := false;
end;

procedure TNewElectionForm.OkButtonClick(Sender: TObject);
var
  name : string;
  randState : string;
begin
  name := ElectionName.Text;
  if name = '' then
    ShowMessage('You must enter a new election name')
  else
  begin
    name := ParentDirectory.Directory + path_sep + name;
    MkDir(name);
    MkDir(name + path_sep + voter_dir);
    MkDir(name + path_sep + pollworker_dir);
    (* Still need to make the 'trustee' directories. *)
    TopForm.ElectionPath := name;
    TopForm.SetElectionString(
        demo_const.election_config, demo_const.xml_element(
            election_config, '', ''));
    vhti.generate_random_state(
        demo_const.xml_element('RandomSeedKey', '',
            make_random_string(20)), randState);
    TopForm.SetElectionString(demo_const.random_state, randState);
    TopForm.Visible := false;
    ElectionPhasesForm.Visible := true;
    Visible := false;
  end;
end;

end.
