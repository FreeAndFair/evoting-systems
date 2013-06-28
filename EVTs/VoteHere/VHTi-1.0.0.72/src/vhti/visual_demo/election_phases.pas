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
unit election_phases;

interface

uses
  Windows, Messages, SysUtils, Variants, Classes, Graphics, Controls, Forms,
  Dialogs, StdCtrls, Buttons;

type
  TElectionPhasesForm = class(TForm)
    PreElection: TBitBtn;
    TransElection: TBitBtn;
    PostElection: TBitBtn;
    procedure FormClose(Sender: TObject; var Action: TCloseAction);
    procedure PreElectionClick(Sender: TObject);
    procedure TransElectionClick(Sender: TObject);
    procedure PostElectionClick(Sender: TObject);
  private
    { Private declarations }
  public
    { Public declarations }
    procedure UpdateState;
  end;

var
  ElectionPhasesForm: TElectionPhasesForm;

implementation

uses
  demo_topform, pre_election, trans_election, demo_const, post_election;

{$R *.dfm}

procedure TElectionPhasesForm.UpdateState;
var
  i : integer;
  HaveAllKeys : boolean;
begin
  HaveAllKeys := true;
  for i := 1 to TopForm.NumAuth do
    HaveAllKeys := HaveAllKeys and
        TopForm.HasElectionString(demo_const.voter(
        'trustee_' + IntToStr(i) + '_' + vv_key));
  PreElection.Enabled := not (HaveAllKeys
      and TopForm.HasElectionString(pollworker(a_bsns))
      and TopForm.HasElectionString(demo_const.signed_blank_ballot));
  TransElection.Enabled := not PreElection.Enabled
      and not TopForm.HasElectionString(polls_closed);
  PostElection.Enabled := TopForm.HasElectionString(polls_closed)
      and not (TopForm.HasElectionString(election_results)
      and TopForm.HasElectionString(revealed_vote_verification_dictionaries));

  PreElectionForm.UpdateState;
  TransElectionForm.UpdateState;
  PostElectionForm.UpdateState;
end;

procedure TElectionPhasesForm.FormClose(Sender: TObject;
  var Action: TCloseAction);
begin
  TopForm.Visible := true;
end;

procedure TElectionPhasesForm.PreElectionClick(Sender: TObject);
begin
  PreElectionForm.UpdateState;
  PreElectionForm.Visible := true;
  Visible := false;
end;

procedure TElectionPhasesForm.TransElectionClick(Sender: TObject);
begin
  TransElectionForm.UpdateState;
  TransElectionForm.Visible := true;
  Visible := false;
end;

procedure TElectionPhasesForm.PostElectionClick(Sender: TObject);
begin
  PostElectionForm.UpdateState;
  PostElectionForm.Visible := true;
  Visible := false;
end;

end.
