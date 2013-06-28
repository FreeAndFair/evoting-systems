object LeoPreElectionForm: TLeoPreElectionForm
  Left = 396
  Top = 402
  Width = 396
  Height = 398
  Caption = 'LEO - Pre Election Operations'
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
    Left = 40
    Top = 8
    Width = 310
    Height = 80
    Alignment = taCenter
    Caption = 
      'Before the election, the LEO needs to establish the cryptographi' +
      'c parameters, publish a digital certificate, and create and sign' +
      ' a blank ballot.  The ballot cannot be created until after the T' +
      'rustees have created the Election Public Key.'
    WordWrap = True
  end
  object GenerateCGP: TCheckBox
    Left = 16
    Top = 112
    Width = 313
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Generate Crypto Group Parameters'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 0
    OnClick = GenerateCGPClick
  end
  object showKeygenParams: TBitBtn
    Left = 344
    Top = 112
    Width = 25
    Height = 25
    Caption = 'OO'
    TabOrder = 1
    OnClick = showDataClick
  end
  object CreateKeys: TCheckBox
    Left = 16
    Top = 144
    Width = 313
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Generate PKI Keys'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 2
    OnClick = CreateKeysClick
  end
  object showPubKey: TBitBtn
    Left = 344
    Top = 144
    Width = 25
    Height = 25
    Caption = 'OO'
    TabOrder = 3
    OnClick = showDataClick
  end
  object CreateSkeleton: TCheckBox
    Left = 16
    Top = 176
    Width = 313
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Import Ballot Skeleton'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 4
    OnClick = CreateSkeletonClick
  end
  object showBallotSkeleton: TBitBtn
    Left = 344
    Top = 176
    Width = 25
    Height = 25
    Caption = 'OO'
    TabOrder = 5
    OnClick = showDataClick
  end
  object CreateBallot: TCheckBox
    Left = 16
    Top = 240
    Width = 313
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Generate Ballot'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 8
    OnClick = CreateBallotClick
  end
  object showBallot: TBitBtn
    Left = 344
    Top = 240
    Width = 25
    Height = 25
    Caption = 'OO'
    TabOrder = 9
    OnClick = showDataClick
  end
  object SignBallot: TCheckBox
    Left = 16
    Top = 272
    Width = 313
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Sign Ballot'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 10
    OnClick = SignBallotClick
  end
  object showSignedBallot: TBitBtn
    Left = 344
    Top = 272
    Width = 25
    Height = 25
    Caption = 'OO'
    TabOrder = 11
    OnClick = showDataClick
  end
  object CreateBSNs: TCheckBox
    Left = 16
    Top = 304
    Width = 313
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Generate BSNs'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 12
    OnClick = CreateBSNsClick
  end
  object showBSNs: TBitBtn
    Left = 344
    Top = 304
    Width = 25
    Height = 25
    Caption = 'OO'
    TabOrder = 13
    OnClick = showDataClick
  end
  object CreateCEP: TCheckBox
    Left = 16
    Top = 208
    Width = 313
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Generate Crypto Election Parameters'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 6
    OnClick = CreateCEPClick
  end
  object showCEP: TBitBtn
    Left = 344
    Top = 208
    Width = 25
    Height = 25
    Caption = 'OO'
    TabOrder = 7
    OnClick = showDataClick
  end
  object InstallBallotBSN: TCheckBox
    Left = 16
    Top = 336
    Width = 313
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Install Ballot and BSNs to Vote Machines'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 14
    OnClick = InstallBallotBSNClick
  end
end
