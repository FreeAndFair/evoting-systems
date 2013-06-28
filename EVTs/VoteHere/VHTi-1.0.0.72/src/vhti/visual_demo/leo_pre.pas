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
unit leo_pre;

interface

uses
  Windows, Messages, SysUtils, Variants, Classes, Graphics, Controls, Forms,
  Dialogs, StdCtrls, Buttons, xmldom, XMLIntf, XMLDoc;

type
  TTAction = Procedure(Sender : TObject) of object;
  TLeoPreElectionForm = class(TForm)
    GenerateCGP: TCheckBox;
    Label1: TLabel;
    showKeygenParams: TBitBtn;
    CreateKeys: TCheckBox;
    showPubKey: TBitBtn;
    CreateSkeleton: TCheckBox;
    showBallotSkeleton: TBitBtn;
    CreateBallot: TCheckBox;
    showBallot: TBitBtn;
    SignBallot: TCheckBox;
    showSignedBallot: TBitBtn;
    CreateBSNs: TCheckBox;
    showBSNs: TBitBtn;
    CreateCEP: TCheckBox;
    showCEP: TBitBtn;
    InstallBallotBSN: TCheckBox;
    procedure FormCreate(Sender: TObject);
    procedure ShowDataClick(Sender: TObject);
    procedure GenerateCGPClick(Sender: TObject);
    procedure CreateKeysClick(Sender: TObject);
    procedure CreateSkeletonClick(Sender: TObject);
    procedure CreateCEPClick(Sender: TObject);
    procedure CreateBallotClick(Sender: TObject);
    procedure SignBallotClick(Sender: TObject);
    procedure CreateBSNsClick(Sender: TObject);
    procedure InstallBallotBSNClick(Sender: TObject);
    procedure FormClose(Sender: TObject; var Action: TCloseAction);
  private
    { Private declarations }
  public
    { Public declarations }
    updating : boolean;
    procedure UpdateState;
    procedure DoStep(Action : TTAction; Sender : TObject);
    (* The worker functions *)
    procedure GenerateCGPWork(Sender: TObject);
    procedure CreateKeysWork(Sender: TObject);
    procedure CreateSkeletonWork(Sender: TObject);
    procedure CreateCEPWork(Sender: TObject);
    procedure CreateBallotWork(Sender: TObject);
    procedure SignBallotWork(Sender: TObject);
    procedure CreateBSNsWork(Sender: TObject);
    procedure InstallBallotBSNWork(Sender: TObject);
  end;

var
  LeoPreElectionForm: TLeoPreElectionForm;

implementation

uses seed_params, demo_topform, demo_const, pre_election, vh_support, vhti,
  ident_info, ballot_skeleton, create_bsn, xml_display;

{$R *.dfm}

procedure TLeoPreElectionForm.UpdateState;
var
  haveAllCommittments : boolean;
  i : integer;
begin
  updating := true;
  
  (* The easy ones first: the 'show' buttons. *)
  SetEnabledForShow(showKeygenParams);
  SetEnabledForShow(showPubKey);
  SetEnabledForShow(showBallotSkeleton);
  SetEnabledForShow(showCEP);
  SetEnabledForShow(showBallot);
  SetEnabledForShow(showSignedBallot);
  SetEnabledForShow(showBSNs);

  (* Slightly harder: the 'done' status. *)
  SetCheckedForDone(GenerateCGP, demo_const.keygen_params);
  SetCheckedForDone(CreateKeys, demo_const.leo_pub_key);
  SetCheckedForDone(CreateSkeleton, demo_const.ballot_skeleton);
  SetCheckedForDone(CreateCEP, demo_const.cep);
  SetCheckedForDone(CreateBallot, demo_const.blank_ballot);
  SetCheckedForDone(SignBallot, demo_const.signed_blank_ballot);
  SetCheckedForDone(CreateBSNs, demo_const.a_bsns);
  SetCheckedForDone(InstallBallotBSN, demo_const.pollworker(p_bsns));

  (* Finally, the enabled next steps. *)
  GenerateCGP.Enabled := not GenerateCGP.Checked;
  CreateKeys.Enabled := not createKeys.Checked;
  CreateSkeleton.Enabled := not CreateSkeleton.Checked;
  haveAllCommittments := true;  (* Well, not so hard just yet. *)
  for i := 1 to TopForm.NumAuth do
  begin
    haveAllCommittments := haveAllCommittments and
        Topform.HasElectionString(demo_const.keyshare_commitment(i));
  end;
  CreateCEP.Enabled := haveAllCommittments
      and TopForm.HasElectionString(demo_const.keygen_params)
      and not CreateCEP.Checked;
  CreateBallot.Enabled := TopForm.HasElectionString(demo_const.cep)
      and TopForm.HasElectionString(demo_const.ballot_skeleton)
      and not CreateBallot.Checked;
  SignBallot.Enabled := TopForm.HasElectionString(demo_const.leo_prv_key)
      and TopForm.HasElectionString(demo_const.blank_ballot)
      and not SignBallot.Checked;
  CreateBSNs.Enabled := not CreateBSNs.Checked;
  InstallBallotBSN.Enabled := TopForm.HasElectionString(
      demo_const.signed_blank_ballot)
      and Topform.HasElectionString(demo_const.a_bsns)
      and not InstallBallotBSN.Checked;

  updating := false;
end;

procedure TLeoPreElectionForm.DoStep(Action : TTAction; Sender : TObject);
begin
  if not updating then
  begin
    Screen.Cursor := crHourGlass;
    Action(Sender);
    Screen.Cursor := crDefault;
    TopForm.UpdateState;
  end;
end;

procedure TLeoPreElectionForm.FormCreate(Sender: TObject);
begin
  updating := true;
  showKeygenParams.Hint := demo_const.keygen_params;
  showPubKey.Hint := demo_const.leo_pub_key;
  showBallotSkeleton.Hint := demo_const.ballot_skeleton;
  showCEP.Hint := demo_const.cep;
  showBallot.Hint := demo_const.blank_ballot;
  showSignedBallot.Hint := demo_const.signed_blank_ballot;
  showBSNs.Hint := demo_const.a_bsns;
  updating := false;
end;

procedure TLeoPreElectionForm.showDataClick(Sender: TObject);
begin
  XmlDisplay.ShowFile(TControl(Sender).Hint);
end;

procedure TLeoPreElectionForm.GenerateCGPWork(Sender: TObject);
var
  encoding : string;
  t : integer;
  n : integer;
  i : integer;
  code : integer;
  randomState : string;
  seedParams : string;
  keygenParams : string;
  pubKey, prvKey, ignoreKey : string;
  newAuth : string;
begin
  with seed_params.SeedParametersForm do
  begin
    ShowModal;
    if ModalResult = mrOk then
    begin

      val(EditT.Text, t, code);
      val(EditN.Text, n, code);
      if (n = 0) or (t = 0) or (n < t) then
      begin
        (* There was a problem.  Don't update stuff. *)
        ShowMessage('Your numbers don''t make sense.  Try again.');
      end
      else
      begin
        (* Time to update the config and do some work. *)
        TopForm.Threshold := t;
        TopForm.NumAuth := n;
        TopForm.SetElectionString(demo_const.threshold, EditT.Text);
        TopForm.SetElectionString(demo_const.num_auth, EditN.Text);

        randomState := TopForm.GetElectionString(demo_const.random_state);
        encoding := xml_attr('Encoding', 'DEC');

        seedParams := demo_const.xml_element('SeedParameters', '',
          xml_element('NumAuth', '', EditN.Text)
          + xml_element('Threshold', '', EditT.Text)
          );
        TopForm.SetElectionString('SeedParameters.xml', seedParams);

        vhti.create_keygen_parameters(seedParams, randomState,
            keygenParams, randomState);
        TopForm.SetElectionString(demo_const.keygen_params, keygenParams);
        LeoPreElectionForm.updateState;

        for i := 1 to n do
        begin
          (* Make the 'trustee' directory. *)
          MkDir(TopForm.ElectionPath + path_sep + trustee_dir_prefix + IntToStr(i));

          vhti.generate_keys(demo_const.xml_element('IdentInfo', '',
              'Authority # ' + IntToStr(i)), prvKey, pubKey);
          vhti.create_authority(IntToStr(i), keygenParams, randomState, pubKey,
              ignoreKey, newAuth, randomState);
          TopForm.SetElectionString(demo_const.trustee(i, pub_key), pubKey);
          TopForm.SetElectionString(demo_const.trustee(i, prv_key), prvKey);
          TopForm.SetElectionString(demo_const.trustee(i, authority), newAuth);
        end;

        TopForm.SetElectionString(demo_const.random_state, randomState);
      end;
    end;
  end;
end;

procedure TLeoPreElectionForm.CreateKeysWork(Sender: TObject);
var
  pub : string;
  prv : string;
begin
  with ident_info.IdentInfo do
  begin
    IdentInfoText.Text := '';
    ShowModal;
    if ModalResult = mrOk then
    begin
      vhti.generate_keys(demo_const.xml_element('IdentInfo', '',
          demo_const.xml_entitify(IdentInfoText.Text)), prv, pub);
      TopForm.SetElectionString(demo_const.leo_pub_key, pub);
      TopForm.SetElectionString(demo_const.leo_prv_key, prv);
    end;
  end;
end;

procedure TLeoPreElectionForm.CreateSkeletonWork(Sender: TObject);
begin
  if false then  (* This is the "too complicated for the demo" mode. *)
    with ballot_skeleton.ballotSkeleton do
    begin
      ShowModal;
      if ModalResult = mrOK then
      begin
        { DONE 2 -oandrewb : check on the status of the abstain choices.  Do i need to add them specifically to the ballot skeleton? }
        if UseDefault.Checked then
        begin
          TopForm.SetElectionString(demo_const.ballot_skeleton,
              demo_const.default_ballot_skeleton);
        end
        else (* the "make your own" one instead. *)
        begin
          TopForm.SetElectionString(demo_const.ballot_skeleton,
              xml_element('BallotSkeleton', '',
                xml_element('ElectionID', '', demo_const.eid)
              + xml_element('PrecinctID', '', demo_const.pid)
              + xml_element('QuestionSkeleton', '',
                  xml_element('QuestionTextStructure', '',
                      demo_const.xml_entitify(r1q.Text))
                + xml_element('AnswerSkeleton', '',
                    xml_element('AnswerTextStructure', '',
                        demo_const.xml_entitify(r1c1.Text)))
                + xml_element('AnswerSkeleton', '',
                    xml_element('AnswerTextStructure', '',
                        demo_const.xml_entitify(r1c2.Text))))
              + xml_element('QuestionSkeleton', '',
                  xml_element('QuestionTextStructure', '',
                      demo_const.xml_entitify(r2q.Text))
                + xml_element('AnswerSkeleton', '',
                    xml_element('AnswerTextStructure', '',
                        demo_const.xml_entitify(r2c1.Text)))
                + xml_element('AnswerSkeleton', '',
                    xml_element('AnswerTextStructure', '',
                        demo_const.xml_entitify(r2c2.Text)))
                + xml_element('AnswerSkeleton', '',
                    xml_element('AnswerTextStructure', '',
                        demo_const.xml_entitify(r2c3.Text))))
              + xml_element('BallotTextStructure', '',
                  'This ballot may require careful attention to detail.')));
        end;
      end;
    end;
  (* The real version. *)
  TopForm.SetElectionString(demo_const.ballot_skeleton,
      demo_const.default_ballot_skeleton);
end;

procedure TLeoPreElectionForm.CreateCEPWork(Sender: TObject);
var
  kgp : string;
  kgpStream : TStringStream;
  xmlCGP : TXMLDocument;
  cgp : string;
  publicKey : string;
  i : integer;
  broadcasts : string;
  ctp : string;
  cep : string;
begin
  kgp := TopForm.GetElectionString(demo_const.keygen_params);
  kgpStream := TStringStream.Create(kgp);
  xmlCGP := TXMLDocument.Create(self);
  xmlCGP.LoadFromStream(kgpStream);
  cgp := xmlCGP.DocumentElement.ChildNodes
      .FindNode('CryptoGroupParameters').XML;

  broadcasts := '<BroadcastValues>';
  for i := 1 to TopForm.NumAuth do
    broadcasts := broadcasts + TopForm.GetElectionString(
        demo_const.trustee(i, broadcast_values));
  broadcasts := broadcasts + '</BroadcastValues>';
  vhti.generate_public_key(kgp, broadcasts, publicKey);
  TopForm.SetElectionString(demo_const.election_pub_key, publicKey);

  ctp := publicKey
      + demo_const.xml_element('NumAuth', '', TopForm.NumAuth)
      + demo_const.xml_element('Threshold', '', Topform.Threshold);
  for i := 1 to TopForm.NumAuth do
    ctp := ctp + TopForm.GetElectionString(demo_const.keyshare_commitment(i));
  ctp := demo_const.xml_element('CryptoTabulationParameters', '', ctp);

  cep := demo_const.xml_element('CryptoElectionParameters', '',
      cgp + ctp);
  TopForm.SetElectionString(demo_const.cep, cep);
end;

procedure TLeoPreElectionForm.CreateBallotWork(Sender: TObject);
var
  ae : string;
  blank_ballot : string;
begin
  ae := demo_const.xml_element('AlphabetEncoding', '', 'BASE64');
  vhti.generate_blank_ballot(
      TopForm.GetElectionString(demo_const.ballot_skeleton),
      TopForm.GetElectionString(demo_const.cep),
      ae, blank_ballot);
  TopForm.SetElectionString(demo_const.blank_ballot, blank_ballot);
end;

procedure TLeoPreElectionForm.SignBallotWork(Sender: TObject);
var
  signed_ballot : string;
begin
  vhti.sign_xml(TopForm.GetElectionString(demo_const.leo_prv_key),
      TopForm.GetElectionString(demo_const.blank_ballot),
      signed_ballot);
  TopForm.SetElectionString(demo_const.signed_blank_ballot, signed_ballot);
end;

procedure TLeoPreElectionForm.CreateBSNsWork(Sender: TObject);
var
  random_state : string;
  authorized : string;
  provisional : string;
begin
  random_state := TopForm.GetElectionString(demo_const.random_state);
  with create_bsn.CreateBSNsForm do
  begin
    ShowModal;
    if ModalResult = mrOk then
    begin
      vhti.generate_bsns(demo_const.xml_element('ElectionID', '', eid),
          demo_const.xml_element('PrecinctID', '', pid),
          StrToInt(numAuthorized.Text), StrToInt(numProvisional.Text),
          random_state, authorized, provisional, random_state);
      TopForm.SetElectionString(demo_const.a_bsns, authorized);
      TopForm.SetElectionString(demo_const.p_bsns, provisional);
      TopForm.SetElectionString(demo_const.random_state, random_state);
    end;
  end;
end;

procedure TLeoPreElectionForm.InstallBallotBSNWork(Sender: Tobject);
begin
  TopForm.SetElectionString(demo_const.pollworker(a_bsns),
      TopForm.GetElectionString(demo_const.a_bsns));
  TopForm.SetElectionString(demo_const.pollworker(p_bsns),
      TopForm.GetElectionString(demo_const.p_bsns));
end;

procedure TLeoPreElectionForm.GenerateCGPClick(Sender: TObject);
begin
  DoStep(GenerateCGPWork, Sender);
end;

procedure TLeoPreElectionForm.CreateKeysClick(Sender: TObject);
begin
  DoStep(CreateKeysWork, Sender);
end;

procedure TLeoPreElectionForm.CreateSkeletonClick(Sender: TObject);
begin
  DoStep(CreateSkeletonWork, Sender);
end;

procedure TLeoPreElectionForm.CreateCEPClick(Sender: TObject);
begin
  DoStep(CreateCEPWork, Sender);
end;

procedure TLeoPreElectionForm.CreateBallotClick(Sender: TObject);
begin
  DoStep(CreateBallotWork, Sender);
end;

procedure TLeoPreElectionForm.SignBallotClick(Sender: TObject);
begin
  DoStep(SignBallotWork, Sender);
end;

procedure TLeoPreElectionForm.CreateBSNsClick(Sender: TObject);
begin
  DoStep(CreateBSNsWork, Sender);
end;

procedure TLeoPreElectionForm.InstallBallotBSNClick(Sender: TObject);
begin
  DoStep(InstallBallotBSNWork, Sender);
end;

procedure TLeoPreElectionForm.FormClose(Sender: TObject;
  var Action: TCloseAction);
begin
  PreElectionForm.Visible := true;
end;

end.
