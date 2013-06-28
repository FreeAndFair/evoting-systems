object ballotSkeleton: TballotSkeleton
  Left = 458
  Top = 362
  BorderStyle = bsDialog
  Caption = 'Define Ballot Skeleton'
  ClientHeight = 341
  ClientWidth = 377
  Color = clBtnFace
  ParentFont = True
  OldCreateOrder = True
  Position = poScreenCenter
  PixelsPerInch = 96
  TextHeight = 13
  object Bevel1: TBevel
    Left = 8
    Top = 8
    Width = 361
    Height = 297
    Shape = bsFrame
  end
  object OKBtn: TButton
    Left = 103
    Top = 308
    Width = 75
    Height = 25
    Caption = 'OK'
    Default = True
    ModalResult = 1
    TabOrder = 0
  end
  object CancelBtn: TButton
    Left = 183
    Top = 308
    Width = 75
    Height = 25
    Cancel = True
    Caption = 'Cancel'
    ModalResult = 2
    TabOrder = 1
  end
  object UseDefault: TRadioButton
    Left = 16
    Top = 24
    Width = 329
    Height = 17
    Caption = 'Use Default Ballot'
    Checked = True
    TabOrder = 2
    TabStop = True
  end
  object ConfigureYourOwn: TRadioButton
    Left = 16
    Top = 48
    Width = 329
    Height = 17
    Caption = 'Configure Your Own'
    TabOrder = 3
  end
  object Panel1: TPanel
    Left = 16
    Top = 72
    Width = 345
    Height = 225
    TabOrder = 4
    object Label1: TLabel
      Left = 16
      Top = 16
      Width = 35
      Height = 13
      Caption = 'Race 1'
    end
    object Label2: TLabel
      Left = 32
      Top = 48
      Width = 53
      Height = 13
      Caption = 'Candidates'
    end
    object Label3: TLabel
      Left = 16
      Top = 104
      Width = 35
      Height = 13
      Caption = 'Race 2'
    end
    object Label5: TLabel
      Left = 32
      Top = 136
      Width = 53
      Height = 13
      Caption = 'Candidates'
    end
    object r1q: TEdit
      Left = 56
      Top = 16
      Width = 273
      Height = 21
      TabOrder = 0
    end
    object r1c1: TEdit
      Left = 88
      Top = 48
      Width = 241
      Height = 21
      TabOrder = 1
    end
    object r1c2: TEdit
      Left = 88
      Top = 72
      Width = 241
      Height = 21
      TabOrder = 2
    end
    object r2q: TEdit
      Left = 56
      Top = 104
      Width = 273
      Height = 21
      TabOrder = 3
    end
    object r2c1: TEdit
      Left = 88
      Top = 136
      Width = 241
      Height = 21
      TabOrder = 4
    end
    object r2c2: TEdit
      Left = 88
      Top = 160
      Width = 241
      Height = 21
      TabOrder = 5
    end
    object r2c3: TEdit
      Left = 88
      Top = 184
      Width = 241
      Height = 21
      TabOrder = 6
    end
  end
end
