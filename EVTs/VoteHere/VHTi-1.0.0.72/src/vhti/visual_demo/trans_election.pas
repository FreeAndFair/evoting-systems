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
unit trans_election;

interface

uses
  Windows, Messages, SysUtils, Variants, Classes, Graphics, Controls, Forms,
  Dialogs, StdCtrls, Buttons;

type
  TTransElectionForm = class(TForm)
    Pollworker: TBitBtn;
    Voter: TBitBtn;
    procedure FormClose(Sender: TObject; var Action: TCloseAction);
    procedure PollworkerClick(Sender: TObject);
    procedure VoterClick(Sender: TObject);
  private
    { Private declarations }
  public
    { Public declarations }
    procedure UpdateState;
  end;

var
  TransElectionForm: TTransElectionForm;

implementation

uses demo_const, demo_topform, election_phases, pollworker_trans,
  voter_trans;

{$R *.dfm}

procedure TTransElectionForm.UpdateState;
begin
  Pollworker.Enabled := TopForm.HasElectionString(demo_const.pollworker(a_bsns));
  Voter.Enabled := TopForm.HasElectionString(demo_const.voter(assigned_bsn))
      and not TopForm.HasElectionString(demo_const.polls_closed);
  PollworkerTransForm.UpdateState;
  VoterTransForm.UpdateState;
end;

procedure TTransElectionForm.FormClose(Sender: TObject;
  var Action: TCloseAction);
begin
  PollworkerTransForm.Visible := false;
  VoterTransForm.Visible := false;
  ElectionPhasesForm.Visible := true;
end;

procedure TTransElectionForm.PollworkerClick(Sender: TObject);
begin
  PollworkerTransForm.Visible := true;
end;

procedure TTransElectionForm.VoterClick(Sender: TObject);
begin
  VoterTransForm.Visible := true;
end;

end.
