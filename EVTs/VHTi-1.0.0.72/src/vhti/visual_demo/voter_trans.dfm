object VoterTransForm: TVoterTransForm
  Left = 524
  Top = 312
  Width = 619
  Height = 166
  Caption = 'Voter - Election Day Operations'
  Color = clBtnFace
  Font.Charset = DEFAULT_CHARSET
  Font.Color = clWindowText
  Font.Height = -11
  Font.Name = 'MS Sans Serif'
  Font.Style = []
  OldCreateOrder = False
  Position = poDesktopCenter
  OnClose = FormClose
  PixelsPerInch = 96
  TextHeight = 13
  object voteNoVV: TBitBtn
    Left = 24
    Top = 16
    Width = 129
    Height = 105
    Caption = 'No Voter Verification'
    TabOrder = 0
    OnClick = voteNoVVClick
  end
  object voteVVscreen: TBitBtn
    Left = 168
    Top = 16
    Width = 129
    Height = 105
    Caption = 'Codes On Screen'
    TabOrder = 1
    OnClick = voteVVscreenClick
  end
  object voteVVpaper: TBitBtn
    Left = 312
    Top = 16
    Width = 129
    Height = 105
    Caption = 'Codes On Paper'
    TabOrder = 2
    OnClick = voteVVpaperClick
  end
  object voteManually: TBitBtn
    Left = 456
    Top = 16
    Width = 129
    Height = 105
    Caption = 'Manually'
    TabOrder = 3
    OnClick = voteManuallyClick
  end
end
