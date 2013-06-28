object ElectionPhasesForm: TElectionPhasesForm
  Left = 394
  Top = 165
  Width = 491
  Height = 166
  Caption = 'Election Phases'
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
  object PreElection: TBitBtn
    Left = 24
    Top = 16
    Width = 129
    Height = 105
    Caption = 'Pre Election'
    TabOrder = 0
    OnClick = PreElectionClick
  end
  object TransElection: TBitBtn
    Left = 176
    Top = 16
    Width = 129
    Height = 105
    Caption = 'Election Day'
    Enabled = False
    TabOrder = 1
    OnClick = TransElectionClick
  end
  object PostElection: TBitBtn
    Left = 328
    Top = 16
    Width = 129
    Height = 105
    Caption = 'Post Election'
    Enabled = False
    TabOrder = 2
    OnClick = PostElectionClick
  end
end
