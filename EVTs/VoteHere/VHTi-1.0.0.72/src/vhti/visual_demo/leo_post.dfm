object LeoPostElectionForm: TLeoPostElectionForm
  Left = 56
  Top = 457
  Width = 493
  Height = 308
  Caption = 'LEO - Post Election Operations'
  Color = clBtnFace
  Font.Charset = DEFAULT_CHARSET
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
    Left = 88
    Top = 8
    Width = 325
    Height = 80
    Caption = 
      'After the election, the LEO needs to authenticate each ballot, t' +
      'hen strip the voter information from them, and compile them into' +
      ' a ballot box.  Later, after the trustees have shuffled and decr' +
      'ypted the ballots, the Leo can report the election results.'
    WordWrap = True
  end
  object AuthenticateBallots: TCheckBox
    Left = 16
    Top = 112
    Width = 409
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Authenticate and Filter Ballots'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 0
    OnClick = AuthenticateBallotsClick
  end
  object showRawBallotBox: TBitBtn
    Left = 440
    Top = 104
    Width = 25
    Height = 25
    Caption = 'OO'
    TabOrder = 1
    OnClick = showDataClick
  end
  object CheckCombinePartialDecrypts: TCheckBox
    Left = 16
    Top = 144
    Width = 409
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Check and Combine Partial Decrypts'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 2
    OnClick = CheckCombinePartialDecryptsClick
  end
  object showClearTextBallots: TBitBtn
    Left = 440
    Top = 136
    Width = 25
    Height = 25
    Caption = 'OO'
    TabOrder = 3
    OnClick = showDataClick
  end
  object GenerateElectionResults: TCheckBox
    Left = 16
    Top = 208
    Width = 409
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Generate Election Results'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 4
    OnClick = GenerateElectionResultsClick
  end
  object showElectionResults: TBitBtn
    Left = 440
    Top = 200
    Width = 25
    Height = 25
    Caption = 'OO'
    TabOrder = 5
    OnClick = showDataClick
  end
  object CheckCombineVcodePartialDecrypts: TCheckBox
    Left = 16
    Top = 176
    Width = 409
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Check and Combine Verification Code Partial Decrypts'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 6
    OnClick = CheckCombineVcodePartialDecryptsClick
  end
  object showVerificationStatements: TBitBtn
    Left = 440
    Top = 168
    Width = 25
    Height = 25
    Caption = 'OO'
    TabOrder = 7
    OnClick = showDataClick
  end
  object showRevealedDictionaries: TBitBtn
    Left = 440
    Top = 232
    Width = 25
    Height = 25
    Caption = 'OO'
    TabOrder = 8
    OnClick = showDataClick
  end
  object CheckCombineRevealedDictionarySecrets: TCheckBox
    Left = 16
    Top = 240
    Width = 409
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Check and Combine Revealed Dictionary Secrets'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 9
    OnClick = CheckCombineRevealedDictionarySecretsClick
  end
end
