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
unit voter_trans;

interface

uses
  Windows, Messages, SysUtils, Variants, Classes, Graphics, Controls, Forms,
  Dialogs, StdCtrls, Buttons;

type
  TVoterTransForm = class(TForm)
    voteNoVV: TBitBtn;
    voteVVscreen: TBitBtn;
    voteVVpaper: TBitBtn;
    voteManually: TBitBtn;
    procedure FormClose(Sender: TObject; var Action: TCloseAction);
    procedure voteNoVVClick(Sender: TObject);
    procedure voteVVscreenClick(Sender: TObject);
    procedure voteVVpaperClick(Sender: TObject);
    procedure voteManuallyClick(Sender: TObject);
  private
    { Private declarations }
  public
    { Public declarations }
    VerificationCodesOnScreen : boolean;
    VerificationCodesOnPaper : boolean;
    procedure UpdateState;
    procedure MakeVVKeys;
  end;

var
  VoterTransForm: TVoterTransForm;

implementation

uses demo_topform, demo_const, trans_election, voter_preconfig,
  virtual_printer;

{$R *.dfm}

procedure TVoterTransForm.UpdateState;
var
  ButtonsEnabled : boolean;
begin
  (* They're all the same: is there an assigned bsn? *)
  ButtonsEnabled := TopForm.HasElectionString(demo_const.voter(assigned_bsn));
  voteNoVV.Enabled := ButtonsEnabled;
  voteVVscreen.Enabled := ButtonsEnabled;
  voteVVpaper.Enabled := ButtonsEnabled;
  voteManually.Enabled := false and ButtonsEnabled;
end;

procedure TVoterTransForm.MakeVVKeys;
var
  i : integer;
  VVKeys : string;
begin
  if not TopForm.HasElectionString(demo_const.voter(vv_keys)) then
  begin
    for i := 0 to TopForm.NumAuth do
    begin
      VVKeys := VVKeys + TopForm.GetElectionString(demo_const.voter(
          'trustee_' + IntToStr(i) + '_' + vv_key));
    end;
    TopForm.SetElectionString(demo_const.voter(vv_keys),
        xml_element('VoteVerificationKeys', '', VVKeys));
  end;
end;

procedure TVoterTransForm.FormClose(Sender: TObject;
  var Action: TCloseAction);
begin
  TransElectionForm.Visible := true;
end;

procedure TVoterTransForm.voteNoVVClick(Sender: TObject);
begin
  VerificationCodesOnScreen := false;
  VerificationCodesOnPaper := false;
  VoterInterfacePreconfig.StartVoting;
  Visible := false;
end;

procedure TVoterTransForm.voteVVscreenClick(Sender: TObject);
begin
  VerificationCodesOnScreen := true;
  VerificationCodesOnPaper := false;
  VoterInterfacePreconfig.StartVoting;
  Visible := false;
end;

procedure TVoterTransForm.voteVVpaperClick(Sender: TObject);
begin
  VerificationCodesOnScreen := false;
  VerificationCodesOnPaper := true;
  VoterInterfacePreconfig.StartVoting;
  Visible := false;
end;

procedure TVoterTransForm.voteManuallyClick(Sender: TObject);
begin
  ShowMessage('Not implemented.');
end;

end.
