object PreElectionForm: TPreElectionForm
  Left = 377
  Top = 322
  Width = 339
  Height = 166
  Caption = 'Pre Election Roles'
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
  object LEO: TBitBtn
    Left = 24
    Top = 16
    Width = 129
    Height = 105
    Caption = 'LEO'
    Font.Charset = DEFAULT_CHARSET
    Font.Color = clWindowText
    Font.Height = -13
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 0
    OnClick = LEOClick
  end
  object Trustee: TBitBtn
    Left = 176
    Top = 16
    Width = 129
    Height = 105
    Caption = 'Trustee'
    TabOrder = 1
    OnClick = TrusteeClick
  end
end
