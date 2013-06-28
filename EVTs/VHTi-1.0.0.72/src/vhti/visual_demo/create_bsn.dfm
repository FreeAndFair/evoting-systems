object CreateBSNsForm: TCreateBSNsForm
  Left = 550
  Top = 334
  BorderStyle = bsDialog
  Caption = 'Create BSNs'
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
    Left = 56
    Top = 48
    Width = 50
    Height = 13
    Caption = 'Authorized'
  end
  object Label2: TLabel
    Left = 56
    Top = 96
    Width = 51
    Height = 13
    Caption = 'Provisional'
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
  object numAuthorized: TEdit
    Left = 120
    Top = 48
    Width = 121
    Height = 21
    TabOrder = 2
    Text = '10'
  end
  object numProvisional: TEdit
    Left = 120
    Top = 96
    Width = 121
    Height = 21
    TabOrder = 3
    Text = '5'
  end
end
