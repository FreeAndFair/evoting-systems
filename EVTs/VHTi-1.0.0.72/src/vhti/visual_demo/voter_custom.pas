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
unit voter_custom;

interface

uses
  Windows, Messages, SysUtils, Variants, Classes, Graphics, Controls, Forms,
  XMLDoc, Dialogs;

type
  TVoterInterfaceCustom = class(TForm)
  private
    { Private declarations }
  public
    { Public declarations }
    BallotXML : TXMLDocument;
    procedure SetCaptions;
  end;

var
  VoterInterfaceCustom: TVoterInterfaceCustom;

implementation

uses
  demo_const, demo_topform, XMLIntf;

{$R *.dfm}

procedure TVoterInterfaceCustom.SetCaptions;
var
  SignedBallot : string;
  SignedBallotStream : TStringStream;
  SignedBallotXML : TXMLDocument;
  Ballot : string;
  BallotStream : TStringStream;

  function QuestionNode(var qid : string) : IXMLNode;
  var
    i : integer;
    nodes : IXMLNodeCollection;
    node : IXMLNode;
    this_qid : string;
  begin
    node := nil;
    nodes := BallotXML.DocumentElement.ChildNodes.FindNode('Question').Collection;
    for i := 1 to nodes.Count do
    begin
      node := nodes.Nodes[i];
      this_qid := node.Attributes['qid'];
      if this_qid = qid then
      begin
        QuestionNode := node;
        break;
      end;
    end;
  end;

  function QuestionText(var qid : string) : string;
  var
    node : IXMLNode;
  begin
    node := QuestionNode(qid);
    if node <> nil then
      QuestionText := node.Text
    else
      QuestionText := '';
  end;

  function AnswerNode(var qid : string; var aid : string) : IXMLNode;
  var
    qnode : IXMLNode;
    i : integer;
    nodes : IXMLNodeCollection;
    node : IXMLNode;
    this_aid : string;
  begin
    qnode := QuestionNode(qid);
    if qnode = nil then
      AnswerNode := nil
    else
    begin
      node := nil;
      nodes := qnode.ChildNodes.FindNode('Answer').Collection;
      for i := 1 to nodes.Count do
      begin
        node := nodes.Nodes[i];
        this_aid := node.Attributes['aid'];
        if this_aid = aid then
        begin
          AnswerNode := node;
          break;
        end;
      end;
    end;
  end;

  function AnswerText(var qid : string; var aid : string) : string;
  var
    node : IXMLNode;
  begin
    node := AnswerNode(qid, aid);
    if node <> nil then
      AnswerText := node.Text
    else
      AnswerText := '';
  end;

begin
  SignedBallot := TopForm.GetElectionString(demo_const.signed_blank_ballot);
  SignedBallotStream := TStringStream.Create(SignedBallot);
  SignedBallotXML := TXMLDocument.Create(self);
  SignedBallotXML.LoadFromStream(SignedBallotStream);
  Ballot := SignedBallotXML.DocumentElement.ChildNodes.FindNode('contents').Text;
  BallotStream := TStringStream.Create(Ballot);
  BallotXML := TXMLDocument.Create(self);
  BallotXML.LoadFromStream(BallotStream);
end;

end.
