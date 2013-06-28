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
unit trustee_post;

interface

uses
  Windows, Messages, SysUtils, Variants, Classes, Graphics, Controls, Forms,
  Dialogs, StdCtrls, Buttons, XMLDoc;

type
  TTAction = Procedure(Sender : TObject) of object;
  TTrusteePostForm = class(TForm)
    Label1: TLabel;
    Label2: TLabel;
    trusteeID: TComboBox;
    Shuffle: TCheckBox;
    showShuffledRawBallotBox: TBitBtn;
    PartialDecrypt: TCheckBox;
    showAuthorityPartialDecrypt: TBitBtn;
    GeneratePreVerificationCodes: TCheckBox;
    showPreVerificationCodes: TBitBtn;
    PartialDecryptVerificationCodes: TCheckBox;
    showAuthorityPartialDecryptOfVerifications: TBitBtn;
    GenerateRevealedDictionarySecrets: TCheckBox;
    showRevealedDictionarySecrets: TBitBtn;

    procedure FormCreate(Sender: TObject);
    procedure trusteeIDChange(Sender: TObject);
    procedure showDataClick(Sender: TObject);
    procedure ShuffleClick(Sender: TObject);
    procedure PartialDecryptClick(Sender: TObject);
    procedure GeneratePreVerificationCodeClick(Sender: TObject);
    procedure PartialDecryptVerificationCodesClick(Sender: TObject);
    procedure GenerateRevealedDictionarySecretsClick(Sender: TObject);
    procedure FormClose(Sender: TObject; var Action: TCloseAction);
  private
    { Private declarations }
    function TrusteePrefix : string;
  public
    { Public declarations }
    tid : integer;
    authorityInfo : string;
    updating : boolean;
    procedure UpdateState;
    procedure DoStep(Action : TTAction; Sender : TObject);
    (* The worker functions. *)
    procedure ShuffleWork(Sender: TObject);
    procedure PartialDecryptWork(Sender: TObject);
    procedure GeneratePreVerificationCodesWork(sender: TObject);
    procedure PartialDecryptVerificationCodesWork(Sender: TObject);
    procedure GenerateRevealedDictionarySecretsWork(Sender: TObject);
  end;

var
  TrusteePostForm: TTrusteePostForm;

implementation

uses demo_const, demo_topform, vhti, vh_support, xml_display, post_election;

{$R *.dfm}

function TTrusteePostForm.TrusteePrefix : string;
begin
  TrusteePrefix := 'trustee_' + IntToStr(tid) + '_';
end;

procedure TTrusteePostForm.UpdateState;
var
  i : integer;
  HaveAllShuffles : boolean;
  HaveAllVCodeBoxes : boolean;
begin
  updating := true;

  (* The easy ones first: the 'show' buttons. *)
  SetEnabledForShow(showShuffledRawBallotBox);
  SetEnabledForShow(showAuthorityPartialDecrypt);
  SetEnabledForShow(showPreVerificationCodes);
  SetEnabledForShow(showAuthorityPartialDecryptOfVerifications);
  SetEnabledForShow(showRevealedDictionarySecrets);

  (* Slightly harder: the 'done' status. *)
  (* BUGBUG need to append trustee number so we know which one ? *)
  SetCheckedForDone(Shuffle, demo_const.raw_ballot_box_after(tid));
  SetCheckedForDone(PartialDecrypt, demo_const.auth_partial_decrypt(tid));
  SetCheckedForDone(GeneratePreVerificationCodes,
     demo_const.pre_verification_code_box(tid));
  SetCheckedForDone(PartialDecryptVerificationCodes,
     demo_const.auth_partial_decrypt4vcodes(tid));
  SetCheckedForDone(GenerateRevealedDictionarySecrets,
     demo_const.revealed_dictionary_secrets(tid));

  (* Finally, the enabled next steps. *)
  Shuffle.Enabled := TopForm.HasElectionString(raw_ballot_box)
     and not Shuffle.Checked;
  HaveAllShuffles := true;
  for i :=1 to TopForm.NumAuth do
  begin
     if not TopForm.HasElectionString(
     demo_const.shuffle_validity_proof(i)) then
        HaveAllShuffles := false;
  end;
  PartialDecrypt.Enabled := HaveAllShuffles and not PartialDecrypt.Checked;
  GeneratePreVerificationCodes.Enabled :=
     not TopForm.HasElectionString(demo_const.pre_verification_code_box(tid))
     and not GeneratePreVerificationCodes.Checked;
  HaveAllVCodeBoxes := true;
  for i := 1 to TopForm.NumAuth do
  begin
     if not TopForm.HasElectionString(
     demo_const.pre_verification_code_box(i)) then
        HaveAllVCodeBoxes := false;
  end;
  PartialDecryptVerificationCodes.Enabled :=
     HaveAllVCodeBoxes and not PartialDecryptVerificationCodes.Checked;
  GenerateRevealedDictionarySecrets.Enabled :=
     not GenerateRevealedDictionarySecrets.Checked;

  updating := false;
end;

procedure TTrusteePostForm.DoStep(Action : TTAction; Sender : TObject);
begin
  if not updating then
  begin
    Screen.Cursor := crHourGlass;
    Action(Sender);
    Screen.Cursor := crDefault;
    TopForm.UpdateState;
  end;
end;

procedure TTrusteePostForm.FormCreate(Sender: TObject);
begin
  updating := true;
  showShuffledRawBallotBox.Hint := demo_const.raw_ballot_box_after(tid);
  showAuthorityPartialDecrypt.Hint := demo_const.auth_partial_decrypt(tid);
  showPreVerificationCodes.Hint := demo_const.pre_verification_code_box(tid);
  showAuthorityPartialDecryptOfVerifications.Hint :=
     demo_const.auth_partial_decrypt4vcodes(tid);
  showRevealedDictionarySecrets.Hint :=
     demo_const.revealed_dictionary_secrets(tid);
  updating := false;
end;

procedure TTrusteePostForm.showDataClick(Sender: TObject);
begin
  XmlDisplay.ShowFile(TControl(Sender).Hint);
end;

procedure TTrusteePostForm.trusteeIDChange(Sender: TObject);
begin
  (* A cheezy way to get the various fields set right. *)
  Screen.Cursor := crHourGlass;
  tid := trusteeID.ItemIndex + 1;
  authorityInfo := TopForm.GetElectionString(
     demo_const.trustee(tid, authority));

  FormCreate(self);

  Screen.Cursor := crDefault;
  TopForm.UpdateState;
end;

procedure TTrusteePostForm.ShuffleWork(Sender: TObject);
var
  randomState : string;
  shuffleValidityProof : string;
  checkShuffleResult : string;
  rbb_before : string;
  rbb_after : string;
  HaveShuffle : boolean;
  i : integer;
begin
  randomState := TopForm.GetElectionString(demo_const.random_state);

  HaveShuffle := false;
  for i :=1 to TopForm.NumAuth do
  begin
     if TopForm.HasElectionString(demo_const.shuffle_validity_proof(i)) then
        (* This means that we already did at least one shuffle *)
        HaveShuffle := true;
  end;

  if HaveShuffle then
  begin
    rbb_before := TopForm.GetElectionString(demo_const.raw_ballot_box_latest);
    TopForm.SetElectionString(demo_const.raw_ballot_box_before(tid),
       rbb_before);
    for i :=1 to TopForm.NumAuth do
      begin
      if TopForm.HasElectionString(demo_const.raw_ballot_box_after(i)) then
      (* Do the check *)
        begin
        vhti.check_shuffle(
          TopForm.GetElectionString(demo_const.raw_ballot_box_before(i)),
          TopForm.GetElectionString(demo_const.raw_ballot_box_after(i)),
          TopForm.GetElectionString(demo_const.signed_blank_ballot),
          TopForm.GetElectionString(demo_const.leo_pub_key),
          TopForm.GetElectionString(demo_const.shuffle_validity_proof(i)),
          checkShuffleResult);
        end;
      end;
  end
  else
  begin
    (* This is our first shuffle *)
    rbb_before := TopForm.GetElectionString(demo_const.raw_ballot_box);
    TopForm.SetElectionString(demo_const.raw_ballot_box_before(tid),
       rbb_before);
  end;

  vhti.shuffle(
      rbb_before,
      randomState,
      TopForm.GetElectionString(demo_const.signed_blank_ballot),
      TopForm.GetElectionString(demo_const.leo_pub_key),
      rbb_after, randomState, shuffleValidityProof);

  TopForm.SetElectionString(demo_const.raw_ballot_box_after(tid),
    rbb_after);
  TopForm.SetElectionString(demo_const.raw_ballot_box_latest,
    rbb_after);
  TopForm.SetElectionString(demo_const.random_state, randomState);
  TopForm.SetElectionString(demo_const.shuffle_validity_proof(tid),
    shuffleValidityProof);

end;

procedure TTrusteePostForm.PartialDecryptWork(Sender: TObject);
var
  randomState : string;
  authPartialDecrypt : string;
  committedAuthority : string;
  auth : string;
  keyShareCommitment : string;

begin
  (* Build a CommittedAuthority object *)
  auth := TopForm.GetElectionString(demo_const.trustee(tid, authority));
  keyShareCommitment := TopForm.GetElectionString(
    demo_const.keyshare_commitment(tid));

  committedAuthority := auth + keyShareCommitment;
  committedAuthority := demo_const.xml_element(
    'CommittedAuthority', '', committedAuthority);
  TopForm.SetElectionString(demo_const.trustee(tid, committed_authority),
    committedAuthority);
  
  randomState := TopForm.GetElectionString(demo_const.random_state);
  vhti.partial_decrypt(
      TopForm.GetElectionString(demo_const.raw_ballot_box_latest),
      TopForm.GetElectionString(demo_const.signed_blank_ballot),
      TopForm.GetElectionString(demo_const.leo_pub_key),
      TopForm.GetElectionString(demo_const.trustee(tid, committed_authority)),
      TopForm.GetElectionString(demo_const.trustee(tid, secret_share)),
      randomState, authPartialDecrypt, randomState);
  TopForm.SetElectionString(demo_const.auth_partial_decrypt(tid),
    authPartialDecrypt);
  TopForm.SetElectionString(demo_const.random_state, randomState);
end;

procedure TTrusteePostForm.GeneratePreVerificationCodesWork(Sender: TObject);
var
  preVCodeBox : string;
begin

  vhti.generate_pre_verification_results(
          TopForm.GetElectionString(demo_const.trustee(tid, vv_key)),
          TopForm.GetElectionString(demo_const.signed_voted_ballots),
          TopForm.GetElectionString(demo_const.signed_blank_ballot),
          TopForm.GetElectionString(demo_const.leo_pub_key),
          preVCodeBox);

  TopForm.SetElectionString(demo_const.pre_verification_code_box(tid),
     preVCodeBox);
end;

procedure TTrusteePostForm.PartialDecryptVerificationCodesWork(Sender: TObject);
var
  i : integer;
  preVCodeBoxes : string;
  authPartialDecryptOfVerifications : string;
  randomState : string;

begin
    randomState := TopForm.GetElectionString(demo_const.random_state);

    if not
       TopForm.HasElectionString(demo_const.pre_verification_code_boxes)
       then
    begin
      preVCodeBoxes := '';
      for i := 1 to TopForm.NumAuth do
      begin
          preVCodeBoxes := preVCodeBoxes +
             TopForm.GetElectionString(
                demo_const.pre_verification_code_box(i));
      end;
      preVCodeBoxes := demo_const.xml_element(
         'PreVerificationCodeBoxes', '', preVCodeBoxes);
      TopForm.SetElectionString(demo_const.pre_verification_code_boxes,
         preVCodeBoxes);
    end;

    (* Now each trustee does the work *)
    vhti.generate_partial_verification_results(
       TopForm.GetElectionString(demo_const.pre_verification_code_boxes),
       TopForm.GetElectionString(demo_const.signed_blank_ballot),
       TopForm.GetElectionString(demo_const.leo_pub_key),
       TopForm.GetElectionString(demo_const.trustee(tid, committed_authority)),
       TopForm.GetElectionString(demo_const.trustee(tid, secret_share)),
       randomState,
       authPartialDecryptOfVerifications, randomState);

   TopForm.SetElectionString(demo_const.random_state, randomState);
   TopForm.SetElectionString(demo_const.auth_partial_decrypt4vcodes(tid),
    authPartialDecryptOfVerifications);

end;

procedure TTrusteePostForm.GenerateRevealedDictionarySecretsWork(Sender:TObject);
var
  trusteeDictionarySecrets : string;
begin

  vhti.generate_dictionary_secrets(
          TopForm.GetElectionString(demo_const.signed_voted_ballots),
          TopForm.GetElectionString(demo_const.trustee(tid, authority)),
          TopForm.GetElectionString(demo_const.trustee(tid, prv_key)),
          TopForm.GetElectionString(demo_const.trustee(tid, vv_key)),
          TopForm.GetElectionString(demo_const.blank_ballot),
          TopForm.GetElectionString(demo_const.a_bsns),
          trusteeDictionarySecrets);

  TopForm.SetElectionString(demo_const.revealed_dictionary_secrets(tid),
    trusteeDictionarySecrets);
end;

procedure TTrusteePostForm.ShuffleClick(Sender: TObject);
begin
  DoStep(ShuffleWork, Sender);
end;

procedure TTrusteePostForm.PartialDecryptClick(Sender: TObject);
begin
  DoStep(PartialDecryptWork, Sender);
end;

procedure TTrusteePostForm.GeneratePreVerificationCodeClick(Sender: TObject);
begin
  DoStep(GeneratePreVerificationCodesWork, Sender);
end;

procedure TTrusteePostForm.PartialDecryptVerificationCodesClick(Sender: TObject);
begin
  DoStep(PartialDecryptVerificationCodesWork, Sender);
end;

procedure TTrusteePostForm.GenerateRevealedDictionarySecretsClick(Sender: TObject);
begin
  DoStep(GenerateRevealedDictionarySecretsWork, Sender);
end;

procedure TTrusteePostForm.FormClose(Sender: TObject;
  var Action: TCloseAction);
begin
  PostElectionForm.Visible := true;
end;

end.
