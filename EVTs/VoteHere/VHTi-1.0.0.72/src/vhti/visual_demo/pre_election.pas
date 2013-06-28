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
unit pre_election;

interface

uses
  Windows, Messages, SysUtils, Variants, Classes, Graphics, Controls, Forms,
  Dialogs, StdCtrls, Buttons;

type
  TPreElectionForm = class(TForm)
    LEO: TBitBtn;
    Trustee: TBitBtn;
    procedure LEOClick(Sender: TObject);
    procedure TrusteeClick(Sender: TObject);
    procedure FormClose(Sender: TObject; var Action: TCloseAction);
  private
    { Private declarations }
  public
    { Public declarations }
    procedure UpdateState;
  end;

var
  PreElectionForm: TPreElectionForm;

implementation

uses
  leo_pre, demo_topform, demo_const, trustee_pre, election_phases;

{$R *.dfm}

procedure TPreElectionForm.LEOClick(Sender: TObject);
begin
  LeoPreElectionForm.UpdateState;
  LeoPreElectionForm.Visible := true;
end;

procedure TPreElectionForm.UpdateState;
begin
  LEO.Enabled := true;
  Trustee.Enabled := TopForm.HasElectionString(demo_const.keygen_params);
  (* Update the 'child' window. *)
  LeoPreElectionForm.UpdateState;
  TrusteePreForm.UpdateState;
end;

procedure TPreElectionForm.TrusteeClick(Sender: TObject);
var
  n, i : integer;
begin
  with TrusteePreForm do
  begin
    trusteeID.Items.Clear;
    n := StrToInt(TopForm.GetElectionString(demo_const.num_auth));
    for i := 1 to n do trusteeID.Items.Add(IntToStr(i));
    trusteeID.ItemIndex := 0;
    trusteeIDChange(self);
  end;
  TrusteePreForm.Visible := true;
end;

procedure TPreElectionForm.FormClose(Sender: TObject;
  var Action: TCloseAction);
begin
  LeoPreElectionForm.Visible := false;
  TrusteePreForm.Visible := false;
  ElectionPhasesForm.Visible := true;
end;

end.
