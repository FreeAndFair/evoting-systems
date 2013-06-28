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
unit pollworker_trans;

interface

uses
  Windows, Messages, SysUtils, Variants, Classes, Graphics, Controls, Forms,
  Dialogs, StdCtrls, Buttons, ExtCtrls, XMLDoc;

type
  TTAction = Procedure(Sender : TObject) of object;
  TPollworkerTransForm = class(TForm)
    Label1: TLabel;
    OpenPolls: TCheckBox;
    AssignBSN: TCheckBox;
    showBSN: TBitBtn;
    ClosePollsAndTransmitBB: TCheckBox;
    showBB: TBitBtn;
    procedure FormCreate(Sender: TObject);
    procedure showDataClick(Sender: TObject);
    procedure OpenPollsClick(Sender: TObject);
    procedure AssignBSNClick(Sender: TObject);
    procedure ClosePollsAndTransmitBBClick(Sender: TObject);
    procedure FormClose(Sender: TObject; var Action: TCloseAction);
  private
    { Private declarations }
    BSNList : TXMLDocument;
  public
    { Public declarations }
    updating : boolean;
    procedure UpdateState;
    procedure DoStep(Action : TTAction; Sender : TObject);
    (* The worker functions *)
    procedure OpenPollsWork(Sender: TObject);
    procedure AssignBSNWork(Sender: TObject);
    procedure ClosePollsAndTransmitBBWork(Sender: TObject);
  end;

var
  PollworkerTransForm: TPollworkerTransForm;

implementation

uses demo_const, demo_topform, xml_display, trans_election, XMLIntf,
  voter_trans;

{$R *.dfm}

procedure TPollworkerTransForm.UpdateState;
var
  BSNAvailable : boolean;
  ss : TStringStream;
  i : integer;
  bsn : IXMLNode;
  bsns : IXMLNodeList;
  used : OleVariant;
begin
  updating := true;
  BSNAvailable := false;

  (* The easy ones first: the 'show' buttons. *)
  SetEnabledForShow(ShowBSN);
  SetEnabledForShow(showBB);

  (* Slightly harder, the 'done' status. *)
  SetCheckedForDone(OpenPolls, demo_const.polls_opened);
  SetCheckedForDone(AssignBSN, demo_const.voter(assigned_bsn));
  SetCheckedForDone(ClosePollsAndTransmitBB, demo_const.polls_closed);

  (* Finally, the enabled next steps. *)
  (* This section is repeated in the BSN Work module *)
  if TopForm.HasElectionString(demo_const.pollworker(a_bsns)) then
    begin
    if BSNList = nil then
    begin
      ss := TStringStream.Create(TopForm.GetElectionString(demo_const.pollworker(a_bsns)));
      BSNList := TXMLDocument.Create(self);
      BSNList.LoadFromStream(ss);
    end;
    bsns := BSNList.DocumentElement.ChildNodes;
    for i := 0 to bsns.Count-1 do
    begin
      bsn := bsns.Get(i);
      used := bsn.Attributes['Assigned'];
      if not VarIsStr(used) or (VarToStr(used) <> 'yes') then
      begin
        BSNAvailable := true;
        break;
      end;
    end;
  end;
  (* End of repeated code *)

  OpenPolls.Enabled := not TopForm.HasElectionString(demo_const.polls_opened);
  AssignBSN.Enabled := TopForm.HasElectionString(demo_const.polls_opened)
      and not TopForm.HasElectionString(demo_const.polls_closed)
      and not TopForm.HasElectionString(demo_const.voter(assigned_bsn))
      and BSNAvailable;
  ClosePollsAndTransmitBB.Enabled := TopForm.HasElectionString(demo_const.polls_opened)
      and not TopForm.HasElectionString(demo_const.polls_closed);

  updating := false;
end;

procedure TPollworkerTransForm.DoStep(Action : TTAction; Sender : TObject);
begin
  if not updating then
  begin
    Screen.Cursor := crHourGlass;
    Action(Sender);
    Screen.Cursor := crDefault;
    Topform.UpdateState;
  end;
end;

procedure TPollworkerTransForm.showDataClick(Sender: TObject);
begin
  XmlDisplay.ShowFile(TControl(Sender).Hint);
end;

procedure TPollworkerTransForm.FormCreate(Sender: TObject);
begin
  updating := True;
  showBSN.Hint := demo_const.voter(assigned_bsn);
  showBB.Hint := demo_const.signed_voted_ballots;

  updating := False;
end;

procedure TPollworkerTransForm.OpenPollsWork(Sender: TObject);
begin
  TopForm.SetElectionString(demo_const.polls_opened,
      demo_const.xml_element('Opened', '', 'True'));
  TopForm.SetElectionString(demo_const.voter(ballot_box), '');
end;

procedure TPollworkerTransForm.AssignBSNWork(Sender: TObject);
var
  ss : TStringStream;
  bsns : IXMLNodeList;
  i : integer;
  bsn : IXMLNode;
  used : OleVariant;
begin
  (* We need to also go fetch the current bsn list. *)
  if BSNList = nil then
  begin
    ss := TStringStream.Create(TopForm.GetElectionString(demo_const.pollworker(a_bsns)));
    BSNList := TXMLDocument.Create(self);
    BSNList.LoadFromStream(ss);
  end;
  (* Grab a bsn and give it to the voter. *)
  bsns := BSNList.DocumentElement.ChildNodes;
  for i := 0 to bsns.Count-1 do
  begin
    bsn := bsns.Get(i);
    used := bsn.Attributes['Assigned'];
    if not VarIsStr(used) or (VarToStr(used) <> 'yes') then
      break;

    bsn := nil;  (* So if we never find one, we can tell. *)
  end;
  (* Mark it as assigned in the list and give it to the voter. *)
  if bsn = nil then
  begin
    ShowMessage('It appears that you have run out of authorized BSNs.');
  end
  else
  begin
    TopForm.SetElectionString(demo_const.voter(assigned_bsn), bsn.XML);
    bsn.Attributes['Assigned'] := 'yes';
    (* Save the list back to the file. *)
    TopForm.SetElectionString(demo_const.pollworker(a_bsns), BSNList.DocumentElement.XML);
  end;
end;

procedure TPollworkerTransForm.ClosePollsAndTransmitBBWork(Sender: TObject);
begin
  TopForm.SetElectionString(demo_const.polls_closed,
      demo_const.xml_element('Closed', '', 'True'));
  TopForm.SetElectionString(demo_const.signed_voted_ballots,
      xml_element('SignedVotedBallots', '',
      TopForm.GetElectionString(demo_const.voter(ballot_box))));
  (* No more voting.  Hide the voter form if it's visible. *)
  VoterTransForm.Visible := false;
end;

procedure TPollworkerTransForm.OpenPollsClick(Sender: TObject);
begin
  DoStep(OpenPollsWork, Sender);
end;

procedure TPollworkerTransForm.AssignBSNClick(Sender: TObject);
begin
  DoStep(AssignBSNWork, Sender);
end;

procedure TPollworkerTransForm.ClosePollsAndTransmitBBClick(
  Sender: TObject);
begin
  DoStep(ClosePollsAndTransmitBBWork, Sender);
end;

procedure TPollworkerTransForm.FormClose(Sender: TObject;
  var Action: TCloseAction);
begin
  TransElectionForm.Visible := true;
end;

end.
