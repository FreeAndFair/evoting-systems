object TransElectionForm: TTransElectionForm
  Left = 423
  Top = 300
  Width = 339
  Height = 166
  Caption = 'Election Day Roles'
  Color = clBtnFace
  Font.Charset = DEFAULT_CHARSET
  Font.Color = clWindowText
  Font.Height = -13
  Font.Name = 'Arial'
  Font.Style = []
  OldCreateOrder = False
  Position = poDesktopCenter
  OnClose = FormClose
  PixelsPerInch = 96
  TextHeight = 16
  object Pollworker: TBitBtn
    Left = 24
    Top = 16
    Width = 129
    Height = 105
    Caption = 'Pollworker'
    Font.Charset = DEFAULT_CHARSET
    Font.Color = clWindowText
    Font.Height = -13
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 0
    OnClick = PollworkerClick
  end
  object Voter: TBitBtn
    Left = 176
    Top = 16
    Width = 129
    Height = 105
    Caption = 'Voter'
    TabOrder = 1
    OnClick = VoterClick
  end
end
