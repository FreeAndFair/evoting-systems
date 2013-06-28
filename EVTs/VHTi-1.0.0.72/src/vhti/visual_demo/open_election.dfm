object OpenElectionFrm: TOpenElectionFrm
  Left = 519
  Top = 158
  Width = 395
  Height = 390
  Caption = 'Open Existing Election'
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
  object Label2: TLabel
    Left = 40
    Top = 16
    Width = 303
    Height = 48
    Alignment = taCenter
    Caption = 
      'Created elections will show up as a subdirectory full of XML fil' +
      'es.  Please select the directory which contains your election.'
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
  object OkButton: TButton
    Left = 184
    Top = 312
    Width = 81
    Height = 33
    Caption = '&Ok'
    Default = True
    TabOrder = 1
    OnClick = OkButtonClick
  end
  object CancelButton: TButton
    Left = 280
    Top = 312
    Width = 81
    Height = 33
    Cancel = True
    Caption = '&Cancel'
    TabOrder = 2
    OnClick = CancelButtonClick
  end
  object ParentDrive: TDriveComboBox
    Left = 24
    Top = 72
    Width = 337
    Height = 22
    TabOrder = 3
    OnChange = ParentDriveChange
  end
end
