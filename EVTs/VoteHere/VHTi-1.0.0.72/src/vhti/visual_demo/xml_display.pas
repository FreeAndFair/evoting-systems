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
unit xml_display;

interface

uses
  Windows, Messages, SysUtils, Variants, Classes, Graphics, Controls, Forms,
  Dialogs, OleCtrls, SHDocVw;

type
  TXmlDisplay = class(TForm)
    XmlBrowser: TWebBrowser;
    procedure FormCreate(Sender: TObject);
    procedure FormResize(Sender: TObject);
  private
    { Private declarations }
  public
    { Public declarations }
    procedure ShowFile(name : string);
  end;

var
  XmlDisplay: TXmlDisplay;

implementation

uses demo_topform;

{$R *.dfm}

procedure TXmlDisplay.ShowFile(name : string);
begin
  Visible := false;
  Caption := name + ' Display Window';
  XmlBrowser.Navigate('file://' + TopForm.FilenameForElectionString(name));
  Visible := true;
end;

procedure TXmlDisplay.FormCreate(Sender: TObject);
begin
  FormResize(self);
end;

procedure TXmlDisplay.FormResize(Sender: TObject);
begin
  XmlBrowser.Width := ClientWidth;
  XmlBrowser.Height := ClientHeight;
end;

end.
