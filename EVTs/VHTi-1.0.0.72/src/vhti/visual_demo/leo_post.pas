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
unit leo_post;

interface

uses
  Windows, Messages, SysUtils, Variants, Classes, Graphics, Controls, Forms,
  Dialogs, StdCtrls, Buttons, xmldom, XMLIntf, XMLDoc;

type
  TTAction = Procedure(Sender : TObject) of object;
  TLeoPostElectionForm = class(TForm)
    Label1: TLabel;
    AuthenticateBallots: TCheckBox;
    showRawBallotBox: TBitBtn;
    CheckCombinePartialDecrypts: TCheckBox;
    showClearTextBallots: TBitBtn;
    GenerateElectionResults: TCheckBox;
    showElectionResults: TBitBtn;
    CheckCombineVcodePartialDecrypts: TCheckBox;
    showVerificationStatements: TBitBtn;
    CheckCombineRevealedDictionarySecrets: TCheckBox;
    showRevealedDictionaries: TBitBtn;
    procedure FormCreate(Sender: TObject);
    procedure ShowDataClick(Sender: TObject);
    procedure AuthenticateBallotsClick(Sender: TObject);
    procedure CheckCombinePartialDecryptsClick(Sender: TObject);
    procedure GenerateElectionResultsClick(Sender: TObject);
    procedure CheckCombineVcodePartialDecryptsClick(Sender: TObject);
    procedure CheckCombineRevealedDictionarySecretsClick(Sender: TObject);
    procedure FormClose(Sender: TObject; var Action: TCloseAction);
  private
    { Private declarations }
  public
    { Public declarations }
    updating : boolean;
    procedure UpdateState;
    procedure DoStep(Action : TTAction; Sender : TObject);
    (* The worker functions *)
    procedure AuthenticateBallotsWork(Sender: TObject);
    procedure CheckCombinePartialDecryptsWork(Sender: TObject);
    procedure GenerateElectionResultsWork(Sender: TObject);
    procedure CheckCombineVcodePartialDecryptsWork(Sender: TObject);
    procedure CheckCombineRevealedDictionarySecretsWork(Sender: TObject);
  end;

var
  LeoPostElectionForm: TLeoPostElectionForm;

implementation

uses seed_params, demo_topform, demo_const, post_election, vh_support, vhti,
  ident_info, ballot_skeleton, create_bsn, xml_display;

{$R *.dfm}

procedure TLeoPostElectionForm.UpdateState;
var
  haveAllPartialDecrypts : boolean;
  haveAllPartialDecrypts4VCodes : boolean;
  haveAllTrusteeRevealedDictionarySecrets : boolean;
  i : integer;
begin
  updating := true;
  
  (* The easy ones first: the 'show' buttons. *)
  SetEnabledForShow(showRawBallotBox);
  SetEnabledForShow(showClearTextBallots);
  SetEnabledForShow(showElectionResults);
  SetEnabledForShow(showVerificationStatements);
  SetEnabledForShow(showRevealedDictionaries);

  (* Slightly harder: the 'done' status. *)
  SetCheckedForDone(AuthenticateBallots, demo_const.raw_ballot_box);
  SetCheckedForDone(CheckCombinePartialDecrypts, demo_const.clear_text_ballots);
  SetCheckedForDone(GenerateElectionResults, demo_const.election_results);
  SetCheckedForDone(CheckCombineVcodePartialDecrypts, demo_const.verification_statements);
  SetCheckedForDone(CheckCombineRevealedDictionarySecrets,
    demo_const.revealed_vote_verification_dictionaries);

  (* Finally, the enabled next steps. *)
  (*  Maybe don't need to check explicitly
  AuthenticateBallots.Enabled := TopForm.HasElectionString(demo_const.signed_voted_ballots);
  *)
  AuthenticateBallots.Enabled := not AuthenticateBallots.Checked;
  haveAllPartialDecrypts := true;
  for i := 1 to TopForm.NumAuth do
     begin
       haveAllPartialDecrypts := haveAllPartialDecrypts and
           Topform.HasElectionString(demo_const.auth_partial_decrypt(i));
     end;
  CheckCombinePartialDecrypts.Enabled := haveAllPartialDecrypts
     and not CheckCombinePartialDecrypts.Checked;
  GenerateElectionResults.Enabled := not GenerateElectionResults.Checked
     and Topform.HasElectionString(demo_const.clear_text_ballots);
  haveAllPartialDecrypts4VCodes := true;
  for i := 1 to TopForm.NumAuth do
     begin
       if not TopForm.HasElectionString(
         demo_const.auth_partial_decrypt4vcodes(i)) then
         haveAllPartialDecrypts4VCodes := false;
     end;
  CheckCombineVcodePartialDecrypts.Enabled :=
     not CheckCombineVcodePartialDecrypts.Checked
     and haveAllPartialDecrypts4VCodes;

  haveAllTrusteeRevealedDictionarySecrets := true;
  for i := 1 to TopForm.NumAuth do
     begin
       if not TopForm.HasElectionString(
          demo_const.revealed_dictionary_secrets(i)) then
          haveAllTrusteeRevealedDictionarySecrets := false;
       end;

  CheckCombineRevealedDictionarySecrets.Enabled :=
    not CheckCombineRevealedDictionarySecrets.Checked
    and haveAllTrusteeRevealedDictionarySecrets;

  updating := false;
end;

procedure TLeoPostElectionForm.DoStep(Action : TTAction; Sender : TObject);
begin
  if not updating then
  begin
    Screen.Cursor := crHourGlass;
    Action(Sender);
    Screen.Cursor := crDefault;
    TopForm.UpdateState;
  end;
end;

procedure TLeoPostElectionForm.FormCreate(Sender: TObject);
begin
  updating := true;
  showRawBallotBox.Hint := demo_const.raw_ballot_box;
  showClearTextBallots.Hint := demo_const.clear_text_ballots;
  showElectionResults.Hint := demo_const.election_results;
  showVerificationStatements.Hint := demo_const.verification_statements;
  showRevealedDictionaries.Hint :=
    demo_const.revealed_vote_verification_dictionaries;
  updating := false;
end;

procedure TLeoPostElectionForm.showDataClick(Sender: TObject);
begin
  XmlDisplay.ShowFile(TControl(Sender).Hint);
end;

procedure TLeoPostElectionForm.AuthenticateBallotsWork(Sender: TObject);
var
  rawBallotBox : string;
  SignedVotedBallots : string;
  SignedVotedBallotsStream : TStringStream;
  SignedVotedBallotsXML : TXMLDocument;
  i : integer;
  SVBnodes : IXMLNodeList;
  SVBnode : IXMLNode;
  SignedData : IXMLNode;
  votedBallotStream : TStringStream;
  VotedBallotXML : TXMLDocument;
  RVBNode : IXMLNode;
begin
   (* Don't use the VHTI_authenticate since there is no voter_roll in
   the pollsite model.  Instead we check that the ballots are all signed
   by leo_prv_key, then we strip out stuff until we have a rawBallotBox *)
   rawBallotBox := '';

  (* Make sure that each ballot is signed properly. *)
  SignedVotedBallots := TopForm.GetElectionString(demo_const.signed_voted_ballots);
  SignedVotedBallotsStream := TStringStream.Create(SignedVotedBallots);
  SignedVotedBallotsXML := TXMLDocument.Create(self);
  SignedVotedBallotsXML.LoadFromStream(SignedVotedBallotsStream);

   begin
    SVBnode := nil;
    SVBnodes := SignedVotedBallotsXML.DocumentElement.ChildNodes;
    for i := 0 to SVBnodes.Count-1 do
    begin
      SVBnode := SVBnodes.Nodes[i];
      SignedData := SVBnode.ChildNodes.FindNode('SignedData');
      votedBallotStream := TStringStream.Create(SignedData.Text);
      VotedBallotXML := TXMLDocument.Create(self);
      VotedBallotXML.LoadFromStream(votedBallotStream);
      RVBNode := VotedBallotXML.DocumentElement.ChildNodes.
       FindNode('RawVotedBallot');
      rawBallotBox := rawBallotBox + RVBNode.XML;
    end;

     rawBallotBox := demo_const.xml_element('RawBallotBox', '', rawBallotBox);
     TopForm.SetElectionString('raw_ballot_box.xml', rawBallotBox);

   end;
end;

procedure TLeoPostElectionForm.CheckCombinePartialDecryptsWork(Sender: TObject);
var
  i : integer;
  authPartialDecrypts : string;
  partially_decrypted_ballot_box : string;
  clearTextBallots : string;
  combinePartialDecryptResult : string;
begin
      (* Need to put together all of the decrypts *)
      authPartialDecrypts := '';
      for i := 1 to TopForm.NumAuth do
        begin
          authPartialDecrypts := authPartialDecrypts +
            TopForm.GetElectionString(demo_const.auth_partial_decrypt(i));
        end;
      authPartialDecrypts := demo_const.xml_element(
         'AuthorityPartialDecrypts', '', authPartialDecrypts);
      TopForm.SetElectionString('authority_partial_decrypts.xml',
        authPartialDecrypts);

      partially_decrypted_ballot_box :=
         TopForm.GetElectionString(demo_const.raw_ballot_box_latest) +
         authPartialDecrypts;
      partially_decrypted_ballot_box := demo_const.xml_element(
         'PartiallyDecryptedBallotBox', '', partially_decrypted_ballot_box);
      TopForm.SetElectionString('partially_decrypted_ballot_box.xml',
         partially_decrypted_ballot_box);

      vhti.check_partial_decrypts_and_combine(
        TopForm.GetElectionString(demo_const.signed_blank_ballot),
        TopForm.GetElectionString(demo_const.leo_pub_key),
        partially_decrypted_ballot_box,
        clearTextBallots, combinePartialDecryptResult);

      TopForm.SetElectionString(demo_const.clear_text_ballots,
         clearTextBallots);
      TopForm.SetElectionString(demo_const.combine_partial_decrypt_result,
         combinePartialDecryptResult);
end;

procedure TLeoPostElectionForm.CheckCombineVcodePartialDecryptsWork(Sender: TObject);
var
  verificationStatements : string;
  combinePartialDecryptResult : string;
  string_length : integer;
  encoding : string;
  preVCodeBoxes : string;
  authPartialDecrypts4VCodes : string;
  i : integer;
begin
  (* Create PreVerificationCodeBoxes *)
  preVCodeBoxes := '';
  for i := 1 to TopForm.NumAuth do
    begin
      preVCodeBoxes := preVCodeBoxes +
        TopForm.GetElectionString(demo_const.pre_verification_code_box(i));
    end;
  preVCodeBoxes := demo_const.xml_element(
     'PreVerificationCodeBoxes', '', preVCodeBoxes);
  TopForm.SetElectionString(demo_const.pre_verification_code_boxes, preVCodeBoxes);

  (* Create collection of authority partial decrypts for the
     verification codes *)
  authPartialDecrypts4VCodes := '';
  for i := 1 to TopForm.NumAuth do
    begin
      authPartialDecrypts4VCodes := authPartialDecrypts4VCodes +
        TopForm.GetElectionString(demo_const.auth_partial_decrypt4vcodes(i));
    end;
  authPartialDecrypts4VCodes := demo_const.xml_element(
     'AuthorityPartialDecrypts', '', authPartialDecrypts4VCodes);
  TopForm.SetElectionString(demo_const.auth_partial_decrypts4vcodes,
     authPartialDecrypts4VCodes);

  string_length := 32;
  encoding := 'DEC';
  encoding := xml_element('AlphabetEncoding', '', encoding);
  TopForm.SetElectionString(demo_const.encoding, encoding);
  vhti.check_vcode_partial_decrypts_and_combine(
    TopForm.GetElectionString(demo_const.pre_verification_code_boxes),
    TopForm.GetElectionString(demo_const.auth_partial_decrypts4vcodes),
    TopForm.GetElectionString(demo_const.signed_voted_ballots),
    TopForm.GetElectionString(demo_const.signed_blank_ballot),
    TopForm.GetElectionString(demo_const.leo_pub_key),
    string_length,
    encoding,
    verificationStatements, combinePartialDecryptResult);

  TopForm.SetElectionString(demo_const.verification_statements,
   verificationStatements);
  TopForm.SetElectionString(demo_const.combine_partial_decrypt_result,
   combinePartialDecryptResult);

end;

procedure TLeoPostElectionForm.GenerateElectionResultsWork(Sender: TObject);
var
    electionResults : string;
    questionResults : string;
    questionReference : string;
    answerResults : string;
    answerReference : string;
    ClearTextBallotsStream : TStringStream;
    ClearTextBallotsXML : TXMLDocument;
    ClearTextBallotsNodes : IXMLNodeList;
    ClearTextBallotNode : IXMLNode;
    BlankBallotStream : TStringStream;
    BlankBallotXML : TXMLDocument;
    BlankBallotNodes : IXMLNodeList;
    BBallotQuestionNode : IXMLNode;
    BBallotAnswerNode : IXMLNode;
    CTBallotAnswerNode : IXMLNode;
    ctbAnswerReference : string;
    answerCount : integer;
    i : integer;
    j : integer;
    k : integer;
    kk : integer;
begin
  (* Need clear_text_ballots and blank_ballot *)
  electionResults := '';
  BlankBallotStream := TStringStream.Create(
                       TopForm.GetElectionString(demo_const.blank_ballot));
  BlankBallotXML := TXMLDocument.Create(self);
  BlankBallotXML.LoadFromStream(BlankBallotStream);
  BlankBallotNodes := BlankBallotXML.DocumentElement.ChildNodes;

  ClearTextBallotsStream := TStringStream.Create(
    TopForm.GetElectionString(demo_const.clear_text_ballots));
  ClearTextBallotsXML := TXMLDocument.Create(self);
  ClearTextBallotsXML.LoadFromStream(ClearTextBallotsStream);
  ClearTextBallotsNodes := ClearTextBallotsXML.DocumentElement.ChildNodes;

  questionResults := '';
  for i := 0 to BlankBallotNodes.Count-1 do
  begin
    if (BlankBallotNodes.Nodes[i].NodeName = 'BallotQuestion') then
    begin
      BBallotQuestionNode := BlankBallotNodes.Nodes[i];
      questionReference := BBallotQuestionNode.Attributes['QuestionReference'];

      answerResults := '';
      for j := 0 to BBallotQuestionNode.ChildNodes.Count-1 do
      begin

        if (BBallotQuestionNode.ChildNodes.Nodes[j].NodeName =
          'BallotAnswer') then
        begin
          answerCount := 0;
          BBallotAnswerNode := BBallotQuestionNode.ChildNodes.Nodes[j];
          answerReference := BBallotAnswerNode.Attributes['AnswerReference'];

          for k := 0 to ClearTextBallotsNodes.Count-1 do
          begin
            ClearTextBallotNode := ClearTextBallotsNodes.Nodes[k];
            for kk := 0 to ClearTextBallotNode.ChildNodes.Count-1 do
            begin
              CTBallotAnswerNode := ClearTextBallotNode.ChildNodes.Nodes[kk];
              ctbAnswerReference := CTBallotAnswerNode.Text;
              if (ctbAnswerReference = answerReference) then
              begin
                answerCount := answerCount + 1;
              end;
            end;
          end;

          answerResults := answerResults +
            xml_element('AnswerResults',
                        xml_attr('AnswerReference', answerReference),
                        xml_element('Count', xml_attr('Encoding', 'DEC'),
                                    IntToStr(answerCount))
                        );
        end;
      end;
      questionResults := questionResults +
        xml_element('QuestionResults',
                    xml_attr('QuestionReference', questionReference),
                    answerResults);
    end;
  end;
  electionResults := xml_element('ElectionResults', '', questionResults);

  TopForm.SetElectionString(demo_const.election_results, electionResults);
end;

procedure TLeoPostElectionForm.CheckCombineRevealedDictionarySecretsWork(Sender: TObject);
var
  revealedDictionarySecretsCheckResults : string;
  trusteeRevealedDictionarySecretsBox : string;
  revealedVoteVerificationDictionaries : string;
  i : integer;
  checkAllSuccess : boolean;
begin

checkAllSuccess := true;
trusteeRevealedDictionarySecretsBox := '';
for i := 1 to TopForm.NumAuth do
    begin
      vhti.check_dictionary_secrets(
      TopForm.GetElectionString(demo_const.revealed_dictionary_secrets(i)),
      TopForm.GetElectionString(demo_const.vv_p_commits(i)),
      TopForm.GetElectionString(demo_const.trustee(i, pub_key)),
      TopForm.GetElectionString(demo_const.blank_ballot),
      revealedDictionarySecretsCheckResults);

      TopForm.SetElectionString(
         demo_const.revealed_dictionary_secrets_check_results(i),
         revealedDictionarySecretsCheckResults);


      if (pos('Success', revealedDictionarySecretsCheckResults) = 0) then
        begin
          checkAllSuccess := false;
          break;
        end;

      trusteeRevealedDictionarySecretsBox := trusteeRevealedDictionarySecretsBox +
        TopForm.GetElectionString(demo_const.revealed_dictionary_secrets(i));
    end;

    begin
    if (checkAllSuccess = true) then
      trusteeRevealedDictionarySecretsBox := demo_const.xml_element(
      'TrusteeRevealedDictionarySecretsBox', '',
      trusteeRevealedDictionarySecretsBox);

      TopForm.SetElectionString(demo_const.trustee_revealed_dictionary_secrets_box,
        trusteeRevealedDictionarySecretsBox);

      vhti.combine_dictionary_secrets(
        TopForm.GetElectionString(demo_const.trustee_revealed_dictionary_secrets_box),
        TopForm.GetElectionString(demo_const.blank_ballot),
        vvcode_numbits,
        alphabet_encoding,
        revealedVoteVerificationDictionaries);

      TopForm.SetElectionString(demo_const.revealed_vote_verification_dictionaries,
        revealedVoteVerificationDictionaries);
    end;
end;

procedure TLeoPostElectionForm.AuthenticateBallotsClick(Sender: TObject);
begin
  DoStep(AuthenticateBallotsWork, Sender);
end;

procedure TLeoPostElectionForm.CheckCombinePartialDecryptsClick(Sender: TObject);
begin
  DoStep(CheckCombinePartialDecryptsWork, Sender);
end;

procedure TLeoPostElectionForm.GenerateElectionResultsClick(Sender: TObject);
begin
  DoStep(GenerateElectionResultsWork, Sender);
end;

procedure TLeoPostElectionForm.CheckCombineVcodePartialDecryptsClick(Sender: TObject);
begin
  DoStep(CheckCombineVcodePartialDecryptsWork, Sender);
end;

procedure TLeoPostElectionForm.CheckCombineRevealedDictionarySecretsClick(Sender: TObject);
begin
  DoStep(CheckCombineRevealedDictionarySecretsWork, Sender);
end;

procedure TLeoPostElectionForm.FormClose(Sender: TObject;
  var Action: TCloseAction);
begin
  PostElectionForm.Visible := true;
end;

end.
