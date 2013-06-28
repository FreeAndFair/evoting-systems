object TopForm: TTopForm
  Left = 1696
  Top = 154
  Width = 332
  Height = 166
  Caption = 'VHTi Demo'
  Color = clBtnFace
  Font.Charset = DEFAULT_CHARSET
  Font.Color = clWindowText
  Font.Height = -13
  Font.Name = 'Arial'
  Font.Style = []
  OldCreateOrder = False
  Position = poDesktopCenter
  PixelsPerInch = 96
  TextHeight = 16
  object NewElection: TBitBtn
    Left = 24
    Top = 16
    Width = 129
    Height = 105
    Caption = 'New Election'
    TabOrder = 0
    OnClick = NewElectionClick
  end
  object OpenElection: TBitBtn
    Left = 176
    Top = 16
    Width = 129
    Height = 105
    Caption = 'Open Election'
    TabOrder = 1
    OnClick = OpenElectionClick
  end
end
