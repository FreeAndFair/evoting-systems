object SeedParametersForm: TSeedParametersForm
  Left = 721
  Top = 166
  Width = 323
  Height = 243
  Caption = 'Seed Parameters'
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
  object Bevel1: TBevel
    Left = 8
    Top = 8
    Width = 297
    Height = 161
    Shape = bsFrame
  end
  object Label2: TLabel
    Left = 80
    Top = 48
    Width = 113
    Height = 16
    Alignment = taRightJustify
    Caption = 'Number of Trustees'
  end
  object Label3: TLabel
    Left = 32
    Top = 88
    Width = 163
    Height = 16
    Alignment = taRightJustify
    Caption = 'Number required to Tabulate'
  end
  object OKBtn: TButton
    Left = 79
    Top = 180
    Width = 75
    Height = 25
    Caption = 'OK'
    Default = True
    ModalResult = 1
    TabOrder = 0
  end
  object CancelBtn: TButton
    Left = 159
    Top = 180
    Width = 75
    Height = 25
    Cancel = True
    Caption = 'Cancel'
    ModalResult = 2
    TabOrder = 1
  end
  object EditN: TEdit
    Left = 208
    Top = 48
    Width = 81
    Height = 24
    TabOrder = 2
    Text = '3'
  end
  object EditT: TEdit
    Left = 208
    Top = 88
    Width = 81
    Height = 24
    TabOrder = 3
    Text = '2'
  end
end
