object PollworkerTransForm: TPollworkerTransForm
  Left = 359
  Top = 310
  Width = 396
  Height = 232
  Caption = 'Pollworker - Election Day Operations'
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
    Top = 16
    Width = 289
    Height = 48
    Alignment = taCenter
    Caption = 
      'The pollworker'#39's job is to start and stop the voting machines, t' +
      'o authenticate voters, and to randomly assign BSNs from the pool' +
      ' to voters or observers.'
    WordWrap = True
  end
  object OpenPolls: TCheckBox
    Left = 16
    Top = 104
    Width = 313
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Open Polls'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 0
    OnClick = OpenPollsClick
  end
  object AssignBSN: TCheckBox
    Left = 16
    Top = 136
    Width = 313
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Assign BSN'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 1
    OnClick = AssignBSNClick
  end
  object showBSN: TBitBtn
    Left = 344
    Top = 136
    Width = 25
    Height = 25
    Caption = 'OO'
    TabOrder = 2
    OnClick = showDataClick
  end
  object ClosePollsAndTransmitBB: TCheckBox
    Left = 16
    Top = 168
    Width = 313
    Height = 17
    Alignment = taLeftJustify
    Caption = 'Close Polls and Transmit Results'
    Font.Charset = ANSI_CHARSET
    Font.Color = clWindowText
    Font.Height = -16
    Font.Name = 'Arial'
    Font.Style = []
    ParentFont = False
    TabOrder = 3
    OnClick = ClosePollsAndTransmitBBClick
  end
  object showBB: TBitBtn
    Left = 344
    Top = 168
    Width = 25
    Height = 25
    Caption = 'OO'
    TabOrder = 4
    OnClick = showDataClick
  end
end
