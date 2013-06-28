object TrusteePostForm: TTrusteePostForm
  Left = 60
  Top = 82
  Width = 393
  Height = 347
  Caption = 'Trustee Post Election'
  Color = clBtnFace
  Font.Charset = ARABIC_CHARSET
  Font.Color = clWindowText
  Font.Height = -13
  Font.Name = 'Arial'
  Font.Style = []
  OldCreateOrder = False
  Position = poDesktopCenter
  OnClose = FormClose
  OnCreate = FormCreate
  PixelsPerInch = 96
  TextHeight = 16
  object Label1: TLabel
    Left = 48
    Top = 8
    Width = 260
    Height = 64
    Caption = 
      'After the election, the Trustees need to work together to shuffl' +
      'e and decrypt the ballots, and to generate verification statemen' +
      'ts for each ballot.'
    WordWrap = True
  end
  object Label2: TLabel
    Left = 56
    Top = 104
    Width = 102
    Height = 20
    Caption = 'Which Trustee'
    Font.Charset = DEFAULT_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'MS Sans Serif'
    Font.Style = []
    ParentFont = False
  end
  object Shuffle: TCheckBox
    Left = 16
    Top = 144
    Width = 313
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Shuffle Ballots'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 1
    OnClick = ShuffleClick
  end
  object showShuffledRawBallotBox: TBitBtn
    Left = 344
    Top = 144
    Width = 25
    Height = 25
    Caption = 'OO'
    TabOrder = 2
    OnClick = showDataClick
  end
  object PartialDecrypt: TCheckBox
    Left = 16
    Top = 176
    Width = 313
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Partially Decrypt Ballots'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 3
    OnClick = PartialDecryptClick
  end
  object showAuthorityPartialDecrypt: TBitBtn
    Left = 344
    Top = 176
    Width = 25
    Height = 25
    Caption = 'OO'
    TabOrder = 4
    OnClick = showDataClick
  end
  object PartialDecryptVerificationCodes: TCheckBox
    Left = 16
    Top = 240
    Width = 313
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Partially Decrypt Verification Codes'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 5
    OnClick = PartialDecryptVerificationCodesClick
  end
  object showAuthorityPartialDecryptOfVerifications: TBitBtn
    Left = 344
    Top = 240
    Width = 25
    Height = 25
    Caption = 'OO'
    TabOrder = 6
    OnClick = showDataClick
  end
  object trusteeID: TComboBox
    Left = 168
    Top = 104
    Width = 161
    Height = 24
    Style = csDropDownList
    ItemHeight = 16
    TabOrder = 0
    OnChange = trusteeIDChange
  end
  object GeneratePreVerificationCodes: TCheckBox
    Left = 16
    Top = 208
    Width = 313
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Generate Preliminary Verification Codes'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 7
    OnClick = GeneratePreVerificationCodeClick
  end
  object showPreVerificationCodes: TBitBtn
    Left = 344
    Top = 208
    Width = 25
    Height = 25
    Caption = 'OO'
    TabOrder = 8
    OnClick = showDataClick
  end
  object GenerateRevealedDictionarySecrets: TCheckBox
    Left = 16
    Top = 272
    Width = 313
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Generate Revealed Dictionary Secrets'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 9
    OnClick = GenerateRevealedDictionarySecretsClick
  end
  object showRevealedDictionarySecrets: TBitBtn
    Left = 344
    Top = 272
    Width = 25
    Height = 25
    Caption = 'OO'
    TabOrder = 10
    OnClick = showDataClick
  end
end
