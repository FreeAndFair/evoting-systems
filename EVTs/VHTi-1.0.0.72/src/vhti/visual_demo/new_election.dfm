object NewElectionForm: TNewElectionForm
  Left = 940
  Top = 140
  Width = 395
  Height = 430
  Caption = 'Create New Election'
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
  object Label1: TLabel
    Left = 24
    Top = 312
    Width = 130
    Height = 16
    Caption = 'Name of new Election:'
  end
  object Label2: TLabel
    Left = 40
    Top = 16
    Width = 303
    Height = 48
    Alignment = taCenter
    Caption = 
      'Created elections will show up as a subdirectory full of XML fil' +
      'es.  Please select the parent directory and enter the name of yo' +
      'ur new election directory.'
    WordWrap = True
  end
  object ParentDirectory: TDirectoryListBox
    Left = 24
    Top = 104
    Width = 337
    Height = 193
    ItemHeight = 16
    TabOrder = 0
  end
  object ElectionName: TEdit
    Left = 160
    Top = 312
    Width = 201
    Height = 24
    TabOrder = 1
  end
  object OkButton: TButton
    Left = 184
    Top = 344
    Width = 81
    Height = 33
    Caption = '&Ok'
    Default = True
    TabOrder = 2
    OnClick = OkButtonClick
  end
  object CancelButton: TButton
    Left = 280
    Top = 344
    Width = 81
    Height = 33
    Cancel = True
    Caption = '&Cancel'
    TabOrder = 3
    OnClick = CancelButtonClick
  end
  object ParentDrive: TDriveComboBox
    Left = 24
    Top = 72
    Width = 337
    Height = 22
    TabOrder = 4
    OnChange = ParentDriveChange
  end
end
