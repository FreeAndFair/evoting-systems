object TrusteePreForm: TTrusteePreForm
  Left = 476
  Top = 379
  Width = 393
  Height = 398
  Caption = 'Trustee Pre Election'
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
    Left = 56
    Top = 8
    Width = 270
    Height = 80
    Alignment = taCenter
    Caption = 
      'Before the election, the Trustees need to work together to estab' +
      'lish the Election Public Key.  This will involve passing data be' +
      'tween the trustees, and finally returning to the LEO so that the' +
      ' final ballot can be constructed.'
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
  object GenSecretShare: TCheckBox
    Left = 16
    Top = 144
    Width = 313
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Generate Secret Values'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 1
    OnClick = GenSecretShareClick
  end
  object showSecretShare: TBitBtn
    Left = 344
    Top = 144
    Width = 25
    Height = 25
    Caption = 'OO'
    TabOrder = 2
    OnClick = showDataClick
  end
  object GenBroadcastValues: TCheckBox
    Left = 16
    Top = 176
    Width = 313
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Generate Broadcast Values'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 3
    OnClick = GenBroadcastValuesClick
  end
  object showBroadcast: TBitBtn
    Left = 344
    Top = 176
    Width = 25
    Height = 25
    Caption = 'OO'
    TabOrder = 4
    OnClick = showDataClick
  end
  object GenCommittment: TCheckBox
    Left = 16
    Top = 240
    Width = 313
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Generate Committment'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 7
    OnClick = GenCommittmentClick
  end
  object showCommit: TBitBtn
    Left = 344
    Top = 240
    Width = 25
    Height = 25
    Caption = 'OO'
    TabOrder = 8
    OnClick = showDataClick
  end
  object GenVVKey: TCheckBox
    Left = 16
    Top = 272
    Width = 313
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Generate Voter Verification Key'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 9
    OnClick = GenVVKeyClick
  end
  object showVVKey: TBitBtn
    Left = 344
    Top = 272
    Width = 25
    Height = 25
    Caption = 'OO'
    TabOrder = 10
    OnClick = showDataClick
  end
  object GenVVCommittments: TCheckBox
    Left = 16
    Top = 304
    Width = 313
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Generate VV Dictionary Commitments'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 11
    OnClick = GenVVCommittmentsClick
  end
  object showVVCommit: TBitBtn
    Left = 344
    Top = 304
    Width = 25
    Height = 25
    Caption = 'OO'
    TabOrder = 12
    OnClick = showDataClick
  end
  object GenPairwiseSecrets: TCheckBox
    Left = 16
    Top = 208
    Width = 313
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Generate Pairwise Secrets'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 5
    OnClick = GenPairwiseSecretsClick
  end
  object showPairwise: TBitBtn
    Left = 344
    Top = 208
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
  object installVVKey: TCheckBox
    Left = 16
    Top = 336
    Width = 313
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Install VV Key on Vote Machine'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 13
    OnClick = installVVKeyClick
  end
end
