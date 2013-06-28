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
unit voter_preconfig;

interface

uses
  Windows, Messages, SysUtils, Variants, Classes, Graphics, Controls, Forms,
  Dialogs, ComCtrls, StdCtrls, XMLDoc;

type
  TVoterInterfacePreconfig = class(TForm)
    BallotPages: TPageControl;
    TabSheet0: TTabSheet;
    TabSheet1: TTabSheet;
    TabSheet2: TTabSheet;
    TabSheet3: TTabSheet;
    TabSheet4: TTabSheet;
    TabSheet5: TTabSheet;
    TabSheet6: TTabSheet;
    TabSheet7: TTabSheet;
    TabSheet8: TTabSheet;
    TabSheet9: TTabSheet;
    TabSheet10: TTabSheet;
    Confirm: TTabSheet;
    Cand00: TRadioButton;
    Cand01: TRadioButton;
    Cand02: TRadioButton;
    Cand03: TRadioButton;
    Cand04: TRadioButton;
    Cand05: TRadioButton;
    Cand06: TRadioButton;
    Cand07: TRadioButton;
    Cand08: TRadioButton;
    Cand09: TRadioButton;
    Cand10: TRadioButton;
    Cand11: TRadioButton;
    Cand12: TRadioButton;
    Cand13: TRadioButton;
    Cand20: TRadioButton;
    Cand21: TRadioButton;
    Cand22: TRadioButton;
    Cand23: TRadioButton;
    Cand24: TRadioButton;
    Cand25: TRadioButton;
    Cand30: TRadioButton;
    Cand31: TRadioButton;
    Cand32: TRadioButton;
    Cand33: TRadioButton;
    Cand34: TRadioButton;
    Cand35: TRadioButton;
    Cand40: TRadioButton;
    Cand41: TRadioButton;
    Cand42: TRadioButton;
    Cand43: TRadioButton;
    Cand44: TRadioButton;
    Cand45: TRadioButton;
    Cand46: TRadioButton;
    Cand47: TRadioButton;
    Cand48: TRadioButton;
    Cand49: TRadioButton;
    Cand410: TRadioButton;
    Cand411: TRadioButton;
    Cand50: TRadioButton;
    Cand51: TRadioButton;
    Cand52: TRadioButton;
    Cand53: TRadioButton;
    Cand54: TRadioButton;
    Cand60: TRadioButton;
    Cand61: TRadioButton;
    Cand62: TRadioButton;
    Cand63: TRadioButton;
    Cand70: TRadioButton;
    Cand71: TRadioButton;
    Cand72: TRadioButton;
    Cand73: TRadioButton;
    Cand74: TRadioButton;
    Cand75: TRadioButton;
    Cand80: TRadioButton;
    Cand81: TRadioButton;
    Cand82: TRadioButton;
    Cand83: TRadioButton;
    Cand84: TRadioButton;
    Cand85: TRadioButton;
    Cand86: TRadioButton;
    Cand87: TRadioButton;
    Cand88: TRadioButton;
    Cand89: TRadioButton;
    Cand91: TRadioButton;
    Cand90: TRadioButton;
    Cand92: TRadioButton;
    Cand93: TRadioButton;
    Cand94: TRadioButton;
    Cand95: TRadioButton;
    Cand100: TRadioButton;
    Cand101: TRadioButton;
    Cand102: TRadioButton;
    Cand103: TRadioButton;
    Cand104: TRadioButton;
    Cand105: TRadioButton;
    Conf00: TStaticText;
    Conf01: TStaticText;
    Conf02: TStaticText;
    Conf03: TStaticText;
    Conf04: TStaticText;
    Conf05: TStaticText;
    Conf06: TStaticText;
    Conf08: TStaticText;
    Conf07: TStaticText;
    Conf09: TStaticText;
    Conf10: TStaticText;
    Conf11: TStaticText;
    Conf12: TStaticText;
    Conf13: TStaticText;
    Conf20: TStaticText;
    Conf21: TStaticText;
    Conf22: TStaticText;
    Conf23: TStaticText;
    Conf24: TStaticText;
    Conf25: TStaticText;
    Conf30: TStaticText;
    Conf31: TStaticText;
    Conf32: TStaticText;
    Conf33: TStaticText;
    Conf34: TStaticText;
    Conf35: TStaticText;
    Conf40: TStaticText;
    Conf41: TStaticText;
    Conf42: TStaticText;
    Conf43: TStaticText;
    Conf44: TStaticText;
    Conf45: TStaticText;
    Conf46: TStaticText;
    Conf47: TStaticText;
    Conf48: TStaticText;
    Conf49: TStaticText;
    Conf410: TStaticText;
    Conf411: TStaticText;
    Conf50: TStaticText;
    Conf51: TStaticText;
    Conf52: TStaticText;
    Conf53: TStaticText;
    Conf54: TStaticText;
    Conf60: TStaticText;
    Conf61: TStaticText;
    Conf62: TStaticText;
    Conf63: TStaticText;
    Conf70: TStaticText;
    Conf71: TStaticText;
    Conf72: TStaticText;
    Conf73: TStaticText;
    Conf74: TStaticText;
    Conf75: TStaticText;
    Conf80: TStaticText;
    Conf81: TStaticText;
    Conf82: TStaticText;
    Conf83: TStaticText;
    Conf84: TStaticText;
    Conf85: TStaticText;
    Conf86: TStaticText;
    Conf87: TStaticText;
    Conf88: TStaticText;
    Conf89: TStaticText;
    Conf90: TStaticText;
    Conf91: TStaticText;
    Conf92: TStaticText;
    Conf93: TStaticText;
    Conf94: TStaticText;
    Conf95: TStaticText;
    Conf100: TStaticText;
    Conf101: TStaticText;
    Conf102: TStaticText;
    Conf103: TStaticText;
    Conf104: TStaticText;
    Conf105: TStaticText;
    Label1: TStaticText;
    Label2: TStaticText;
    Label3: TStaticText;
    Label4: TStaticText;
    Label5: TStaticText;
    Label6: TStaticText;
    Label7: TStaticText;
    Label8: TStaticText;
    Label9: TStaticText;
    Label10: TStaticText;
    Label11: TStaticText;
    Cast: TButton;
    CD0: TStaticText;
    CD1: TStaticText;
    CD2: TStaticText;
    CD3: TStaticText;
    CD4: TStaticText;
    CD5: TStaticText;
    CD6: TStaticText;
    CD7: TStaticText;
    CD8: TStaticText;
    CD9: TStaticText;
    CD10: TStaticText;
    procedure FormResize(Sender: TObject);
    procedure ConfirmClick(Sender: TObject);
    procedure FormCreate(Sender: TObject);
    procedure CastClick(Sender: TObject);
    procedure FormClose(Sender: TObject; var Action: TCloseAction);
  private
    { Private declarations }
    BallotXML : TXMLDocument;
(*    function AnswersOnPage(num : integer) : integer; *)
    function SafeFindChild(parent : TWinControl ; name : string) : TControl;
    function FindPage(number : integer) : TTabSheet;
    function FindCandidate(page : integer; number : integer) : TRadioButton;
    function FindConf(page : integer; number : integer) : TStaticText;
    function FindSelectionForPage(page : integer) : integer;
    function FindSelectedCandidateForPage(page : integer) : TRadioButton;
    function FindSelectedConfForPage(page : integer) : TStaticText;
    function CanFindConf(page : integer; num : integer; var FoundConf : TStaticText) : boolean;
    function CanFindCand(page : integer; num : integer; var FoundCand : TRadioButton) : boolean;
    procedure ShowConfirmationCodes;
    procedure SetConfirmationCodes;
    procedure ResetSelections;
  public
    { Public declarations }
    procedure StartVoting;
  end;

var
  VoterInterfacePreconfig: TVoterInterfacePreconfig;

implementation

uses
  demo_const, demo_topform, vh_support, vhti, xmlintf, voter_trans,
  virtual_printer;

{$R *.dfm}

type
  ENotFoundError = class(Exception);

procedure TVoterInterfacePreconfig.ResetSelections;
var
  pageNum : integer;
  answerNum : integer;
  FoundCand : TRadioButton;

begin
   for pageNum := 0 to 10 do
    begin
    answerNum := 0;
    while CanFindCand(pageNum, answerNum, FoundCand) do
    begin
      if (FoundCand.Caption = 'Abstain') then
      begin
        FoundCand.Checked := true;
      end;

      Inc(answerNum);
    end;
    end;
end;

procedure TVoterInterfacePreconfig.StartVoting;
var
  BlankBallot : string;
  BBStream : TStringStream;
begin
  PrinterOutput.Visible := false;
  PrinterOutput.Left := Left + Width;

  BlankBallot := TopForm.GetElectionString(demo_const.blank_ballot);
  BBStream := TStringStream.Create(BlankBallot);
  BallotXML := TXMLDocument.Create(self);
  BallotXML.LoadFromStream(BBStream);
  ResetSelections;
  BallotPages.ActivePage := TabSheet0;

  if VoterTransForm.VerificationCodesOnPaper
      or VoterTransForm.VerificationCodesOnScreen then
    SetConfirmationCodes;

  ShowConfirmationCodes;

  PrinterOutput.Visible := VoterTransForm.VerificationCodesOnPaper;
  Visible := true;
end;

function TVoterInterfacePreconfig.SafeFindChild(parent : TWinControl;
    name : string) : TControl;
var
  control : TControl;
begin
  control := parent.FindChildControl(name);
  if control = nil then
    raise ENotFoundError.Create(name + ' not found');
  SafeFindChild := control;
end;

function TVoterInterfacePreconfig.FindPage(number : integer) : TTabSheet;
begin
  FindPage := TTabSheet(SafeFindChild(BallotPages, 'TabSheet' + IntToStr(number)));
end;

function TVoterInterfacePreconfig.FindCandidate(page : integer;
    number : integer) : TRadioButton;
begin
  FindCandidate := TRadioButton(SafeFindChild(FindPage(page),
      'Cand' + IntToStr(page) + IntToStr(number)));
end;

function TVoterInterfacePreconfig.FindConf(page : integer;
    number : integer) : TStaticText;
begin
  FindConf := TStaticText(SafeFindChild(FindPage(page),
      'Conf' + IntToStr(page) + IntToStr(number)));
end;

function TVoterInterfacePreconfig.CanFindConf(page : integer;
    num : integer; var FoundConf : TStaticText) : boolean;
var
  FoundPage : TTabSheet;
begin
  (* It's unfortunate that the first-chance exception thing jumps in so
     quick making the try/catch type mechanism so ungainly.  Have to
     basically reimplement the SafeFindFoo stuff here. *)
  FoundPage := TTabSheet(BallotPages.FindChildControl(
      'TabSheet' + IntToStr(page)));
  if FoundPage = nil then
    FoundConf := nil
  else
    FoundConf := TStaticText(FoundPage.FindChildControl(
        'Conf' + IntToStr(page) + IntToStr(num)));
  CanFindConf := FoundConf <> nil;
end;

function TVoterInterfacePreconfig.CanFindCand(page : integer;
    num : integer; var FoundCand : TRadioButton) : boolean;
var
  FoundPage : TTabSheet;
begin
  (* It's unfortunate that the first-chance exception thing jumps in so
     quick making the try/catch type mechanism so ungainly.  Have to
     basically reimplement the SafeFindFoo stuff here. *)
  FoundPage := TTabSheet(BallotPages.FindChildControl(
      'TabSheet' + IntToStr(page)));
  if FoundPage = nil then
    FoundCand := nil
  else
    FoundCand := TRadioButton(FoundPage.FindChildControl(
        'Cand' + IntToStr(page) + IntToStr(num)));
  CanFindCand := FoundCand <> nil;
end;

function TVoterInterfacePreconfig.FindSelectionForPage(page : integer) : integer;
var
  i : integer;
begin
  i := 0;
  while not FindCandidate(page, i).Checked do
    i := i + 1;
  FindSelectionForPage := i;
end;

function TVoterInterfacePreConfig.FindSelectedCandidateForPage(page : integer) : TRadioButton;
begin
  FindSelectedCandidateForPage := FindCandidate(page, FindSelectionForPage(page));
end;

function TVoterInterfacePreConfig.FindSelectedConfForPage(page : integer) : TStaticText;
begin
  FindSelectedConfForPage := FindConf(page, FindSelectionForPage(page));
end;

function FindQuestion(BBNodes : IXMLNodeList; Num : integer) : IXmlNode;
var
  i : integer;
  QID : string;
  found : boolean;
begin
  QID := 'Q' + IntToStr(Num);
  found := false;
  for i := 0 to BBNodes.Count - 1 do
  begin
    if (BBNodes.Nodes[i].NodeName = 'BallotQuestion')
        and (BBNodes.Nodes[i].Attributes['QuestionReference'] = QID) then
    begin
      FindQuestion := BBNodes.Nodes[i];
      found := true;
      break;
    end;
  end;
  if not found then
    raise ENotFoundError.Create('Could not find the ' + IntToStr(num) + 'th question.');
end;

function FindAnswer(Question : IXmlNode; Name : string) : string;
var
  i : integer;
  AnswerCandidate, AnswerTextStructure : IXMLNode;
  found : boolean;
begin
  found := false;
  for i := 0 to Question.ChildNodes.Count - 1 do
  begin
    AnswerCandidate := Question.ChildNodes.Nodes[i];
    AnswerTextStructure := AnswerCandidate.ChildNodes.FindNode('AnswerTextStructure');
    if AnswerTextStructure = nil then
      TopForm.SetElectionString('t2.xml', AnswerCandidate.XML)
    else
      TopForm.SetElectionString('t2.xml', AnswerTextStructure.XML);
    if (AnswerCandidate.NodeName = 'BallotAnswer')
        and (AnswerTextStructure <> nil)
        and (AnswerTextStructure.IsTextElement)
        and (AnswerTextStructure.Text = Name) then
    begin
      FindAnswer := AnswerCandidate.Attributes['AnswerReference'];
      found := true;
      break;
    end;
  end;
  if not found then
    raise ENotFoundError.Create('Could not find answer "' + name +
        '" in question: ' + Question.XML);
end;

procedure TVoterInterfacePreconfig.ShowConfirmationCodes;
var
  PageNum : integer;
  AnswerNum : integer;
  FoundConf : TStaticText;
begin
  for PageNum := 0 to 10 do
  begin
    AnswerNum := 0;
    while CanFindConf(PageNum, AnswerNum, FoundConf) do
    begin
      FoundConf.Visible := VoterTransForm.VerificationCodesOnScreen;
      Inc(AnswerNum);
    end;
  end;
end;

procedure TVoterInterfacePreconfig.SetConfirmationCodes;

var
  VVKeys : string;

  procedure MakeVVKeys;
  var
    i : integer;
  begin
    VVKeys := '';
    for i := 1 to TopForm.NumAuth do
    begin
      VVKeys := VVKeys + TopForm.GetElectionString(demo_const.voter(
          trustee_dir_prefix + IntToStr(i) + '_' + vv_key));
    end;
    VVKeys := demo_const.xml_element('VoteVerificationKeys', '', VVKeys);
    TopForm.SetElectionString(demo_const.voter(vv_keys), VVKeys);
  end;

var
  VerificationDictionary : string;
  VDStream : TStringStream;
  VDXML : TXMLDocument;
  DQuestion, DQuestionCand : IXMLNode;
  DQuestionRef : OleVariant;
  QNumber : integer;
  CNumber : integer;
  DCode : IXMLNode;
  ConfControl : TStaticText;
  i : integer;
  found : boolean;
begin
  Screen.Cursor := crHourGlass;

  (* Construct the vv_keys if there isn't one already. *)
  if TopForm.HasElectionString(demo_const.voter(vv_keys)) then
    VVKeys := TopForm.GetElectionString(demo_const.voter(vv_keys))
  else
    MakeVVKeys;

  (* Generate the verification dictionary *)
  if not TopForm.HasElectionString(demo_const.voter(verification_codes)) then
  begin
    vhti.generate_vote_verification_dictionary(
        TopForm.GetElectionString(demo_const.voter(vv_keys)),
        TopForm.GetElectionString(demo_const.blank_ballot),
        TopForm.GetElectionString(demo_const.voter(assigned_bsn)),
        vvcode_numbits,
        alphabet_encoding,
        VerificationDictionary);
    TopForm.SetElectionString(voter(verification_codes), VerificationDictionary);
  end
  else
  begin
    VerificationDictionary := TopForm.GetElectionString(voter(verification_codes));
  end;

  (* Wander thru it, setting the ConfXY captions and making them visible. *)
  VDStream := TStringStream.Create(VerificationDictionary);
  VDXML := TXMLDocument.Create(self);
  VDXML.LoadFromStream(VDStream);

  found := false;
  for QNumber := 0 to 10 do
  begin
    DQuestion := nil;
    for i := 0 to VDXML.DocumentElement.ChildNodes.Count - 1 do
    begin
      DQuestionCand := VDXML.DocumentElement.ChildNodes.Nodes[i];
      DQuestionRef := DQuestionCand.Attributes['QuestionReference'];
      if (DQuestionCand.NodeName = 'DictionaryQuestion')
          and (VarIsStr(DQuestionRef))
          and ('Q' + IntToStr(QNumber) = DQuestionRef) then
      begin
        found := true;
        DQuestion := DQuestionCand;
        break;
      end;
    end;
    if not found then
      raise ENotFoundError.Create('Element not found looking for DictionaryQuestion Q' + IntToStr(QNumber) + ' in ' + VDXML.DocumentElement.XML);
    PrinterOutput.PrintLine('--- ' + FindPage(QNumber).Caption + ' ---');
    for CNumber := 0 to DQuestion.ChildNodes.Count - 1 do
    begin
      DCode := DQuestion.ChildNodes.Nodes[CNumber];
      ConfControl := FindConf(QNumber, CNumber);
      ConfControl.Caption := DCode.Text;
      PrinterOutput.PrintLine('  ' + FindCandidate(QNumber, CNumber).Caption);
      PrinterOutput.Tab(43);
      PrinterOutput.PrintMore(DCode.Text);
    end;
    PrinterOutput.PrintLine('');
  end;
  PrinterOutput.PrintLine('');

  Screen.Cursor := crDefault;
end;

procedure TVoterInterfacePreconfig.FormCreate(Sender: TObject);
begin
  BallotPages.ActivePage := TabSheet0;
end;

procedure TVoterInterfacePreconfig.FormResize(Sender: TObject);
begin
  BallotPages.Top := 0;
  BallotPages.Left := 0;
  BallotPages.Width := ClientWidth;
  BallotPages.Height := ClientHeight;
end;

procedure TVoterInterfacePreconfig.ConfirmClick(Sender: TObject);
var
  SignedVotedBallot : string;
  ClearTextBallot : string;

  procedure ConstructVote;
  var
    BBNodes : IXMLNodeList;
    i : integer;
    CandName : string;
    AnswerRefs : string;
    RandomState : string;
  begin
    (* The choices are in {CD0-10}.Caption, just gather them up, find
       them in the ballot and form the vote. *)
    AnswerRefs := '';
    BBNodes := BallotXML.DocumentElement.ChildNodes;
    for i := 0 to 10 do
    begin
      CandName := TStaticText(SafeFindChild(Confirm, 'CD' + IntToStr(i))).Caption;
      (* Now that I've found the question in the blank ballot, look for this answer. *)
      AnswerRefs := AnswerRefs + xml_element('AnswerReference', '',
          FindAnswer(FindQuestion(BBNodes, i), CandName));
    end;
    ClearTextBallot := xml_element('ClearTextBallot', '', AnswerRefs);
    RandomState := TopForm.GetElectionString(random_state);
    vhti.encrypt_ballot_pollsite(ClearTextBallot,
        TopForm.GetElectionString(blank_ballot),
        TopForm.GetElectionString(voter(assigned_bsn)),
        RandomState,
        TopForm.GetElectionString(leo_prv_key),
        SignedVotedBallot,
        RandomState);
    TopForm.SetElectionString(random_state, RandomState);
    TopForm.SetElectionString(voter(unconfirmed_signed_voted_ballot), SignedVotedBallot);
  end;

  procedure PrintReceipt;
  var
    VoteReceiptData : string;
    i : integer;
    BSNStringStream : TStringStream;
    BSNXML : TXMLDocument;

  begin
    { TODO -oandrewb : Print the receipt body }
    vhti.generate_vote_receipt_data(SignedVotedBallot,
        TopForm.GetElectionString(voter(vv_keys)),
        TopForm.GetElectionString(blank_ballot),
        TopForm.GetElectionString(voter(assigned_bsn)),
        ClearTextBallot,
        vvcode_numbits,
        alphabet_encoding,
        VoteReceiptData);
    TopForm.SetElectionString(voter(receipt_data), VoteReceiptData);

    BSNStringStream := TStringStream.Create(TopForm.GetElectionString(voter(assigned_bsn)));
    BSNXML := TXMLDocument.Create(self);
    BSNXML.LoadFromStream(BSNStringStream);

    PrinterOutput.PrintLine('----------------- CUT ------------------');
    PrinterOutput.PrintLine('Receipt for Ballot Sequence Number: ' + BSNXML.DocumentElement.Text);
    PrinterOutput.PrintLine('');
    for i := 0 to 10 do
    begin
      (* Don't tell anyone, but I'm just using the question captions and
         confirmation codes from the confirmation page, not from the
         receipt data.  There's not really any information in there that we
         need other than the SVBHash...which we don't even show. *)
      PrinterOutput.PrintLine(FindPage(i).Caption);
      PrinterOutput.Tab(43);
      PrinterOutput.PrintMore(FindSelectedConfForPage(i).Caption);
    end;
    PrinterOutput.PrintLine('');
    PrinterOutput.Visible := true;
  end;

var
  i : integer;
begin
  Screen.Cursor := crHourGlass;

  if BallotPages.ActivePage = Confirm then
  begin
    for i := 0 to 10 do
      TStaticText(SafeFindChild(Confirm, 'CD' + IntToStr(i))).Caption :=
          FindSelectedCandidateForPage(i).Caption;
    ConstructVote;
    if VoterTransForm.VerificationCodesOnScreen
        or VoterTransForm.VerificationCodesOnPaper then
      PrintReceipt;
  end;
  Screen.Cursor := crDefault;
end;

procedure TVoterInterfacePreconfig.CastClick(Sender: TObject);
var
  VoteReceipt : string;
  ReceiptStringStream : TStringStream;
  ReceiptXML : TXMLDocument;
  ReceiptNodes : IXMLNodeList;
  SignedDataNode : IXMLNode;
  voteReceiptDataStream : TStringStream;
  VoteReceiptDataXML : TXMLDocument;
  svbHash : string;
  SignatureNode : IXMLNode;
begin
  if VoterTransForm.VerificationCodesOnScreen
        or VoterTransForm.VerificationCodesOnPaper then
  begin
  { TODO -oandrewb : Print the receipt signature. }
    vhti.sign_receipt(TopForm.GetElectionString(voter(receipt_data)),
        TopForm.GetElectionString(leo_prv_key),
        VoteReceipt);
    TopForm.SetElectionString(voter(signed_receipt), VoteReceipt);

    ReceiptStringStream := TStringStream.Create(VoteReceipt);
    ReceiptXML := TXMLDocument.Create(self);
    ReceiptXML.LoadFromStream(ReceiptStringStream);
    ReceiptNodes := ReceiptXML.DocumentElement.ChildNodes;
    SignedDataNode := ReceiptNodes.FindNode('SignedData');

    voteReceiptDataStream := TStringStream.Create(SignedDataNode.Text);
    VoteReceiptDataXML := TXMLDocument.Create(self);
    VoteReceiptDataXML.LoadFromStream(voteReceiptDataStream);
    svbHash := VoteReceiptDataXML.DocumentElement.Attributes['SVBHash'];

    PrinterOutput.PrintLine('Ballot Hash: ' + svbHash);
    PrinterOutput.PrintLine('');
    SignatureNode := ReceiptNodes.FindNode('Signature');
    PrinterOutput.PrintLine('Signature: ' + SignatureNode.Text);
  end;

  { DONE -oandrewb : make the signed voted ballot show up in a ballot box instead of just a file. }
  TopForm.SetElectionString(demo_const.voter(ballot_box),
      TopForm.GetElectionString(demo_const.voter(ballot_box))
      + TopForm.GetElectionString(demo_const.voter(unconfirmed_signed_voted_ballot)));
  TopForm.RemoveElectionString(demo_const.voter(assigned_bsn));

  ShowMessage('Vote has been cast');
  Visible := false;
  TopForm.UpdateState;
end;

procedure TVoterInterfacePreconfig.FormClose(Sender: TObject;
  var Action: TCloseAction);
begin
  PrinterOutput.PrintLine('----------------- CUT ------------------');
  PrinterOutput.Visible := false;
end;

end.
