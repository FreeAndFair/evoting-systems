object IdentInfo: TIdentInfo
  Left = 215
  Top = 128
  BorderStyle = bsDialog
  Caption = 'Identification Information'
  ClientHeight = 214
  ClientWidth = 313
  Color = clBtnFace
  ParentFont = True
  OldCreateOrder = True
  Position = poScreenCenter
  PixelsPerInch = 96
  TextHeight = 13
  object Bevel1: TBevel
    Left = 8
    Top = 8
    Width = 297
    Height = 161
    Shape = bsFrame
  end
  object Label1: TLabel
    Left = 16
    Top = 64
    Width = 144
    Height = 13
    Caption = 'Enter identification information:'
  end
  object OKBtn: TButton
    Left = 79
    Top = 180
    Width = 75
    Height = 25
    Caption = 'OK'
    Default = True
    ModalResult = 1
    TabOrder = 1
  end
  object CancelBtn: TButton
    Left = 159
    Top = 180
    Width = 75
    Height = 25
    Cancel = True
    Caption = 'Cancel'
    ModalResult = 2
    TabOrder = 2
  end
  object IdentInfoText: TEdit
    Left = 16
    Top = 88
    Width = 281
    Height = 21
    TabOrder = 0
  end
end
