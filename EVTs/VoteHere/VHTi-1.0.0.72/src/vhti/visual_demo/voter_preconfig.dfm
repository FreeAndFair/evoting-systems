object VoterInterfacePreconfig: TVoterInterfacePreconfig
  Left = 814
  Top = 228
  Width = 540
  Height = 589
  Caption = 'Voter Interface'
  Color = clBtnFace
  Font.Charset = DEFAULT_CHARSET
  Font.Color = clWindowText
  Font.Height = -19
  Font.Name = 'Arial'
  Font.Style = []
  OldCreateOrder = False
  Position = poDesktopCenter
  OnClose = FormClose
  OnCreate = FormCreate
  OnResize = FormResize
  PixelsPerInch = 96
  TextHeight = 22
  object BallotPages: TPageControl
    Left = 0
    Top = 0
    Width = 521
    Height = 560
    ActivePage = TabSheet1
    MultiLine = True
    Style = tsButtons
    TabOrder = 0
    OnChange = ConfirmClick
    object TabSheet0: TTabSheet
      Caption = 'U.S.Senator'
      object Conf00: TStaticText
        Left = 456
        Top = 8
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 10
        Visible = False
      end
      object Conf01: TStaticText
        Left = 456
        Top = 32
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 11
        Visible = False
      end
      object Conf02: TStaticText
        Left = 456
        Top = 56
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 12
        Visible = False
      end
      object Conf03: TStaticText
        Left = 456
        Top = 80
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 13
        Visible = False
      end
      object Conf04: TStaticText
        Left = 456
        Top = 104
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 14
        Visible = False
      end
      object Conf05: TStaticText
        Left = 456
        Top = 128
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 15
        Visible = False
      end
      object Conf06: TStaticText
        Left = 456
        Top = 152
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 16
        Visible = False
      end
      object Conf08: TStaticText
        Left = 456
        Top = 200
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 17
        Visible = False
      end
      object Conf07: TStaticText
        Left = 456
        Top = 176
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 18
        Visible = False
      end
      object Conf09: TStaticText
        Left = 456
        Top = 344
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 19
        Visible = False
      end
      object Cand00: TRadioButton
        Left = 8
        Top = 8
        Width = 441
        Height = 17
        Caption = 'Maria Cantwell'
        TabOrder = 0
      end
      object Cand01: TRadioButton
        Left = 8
        Top = 32
        Width = 441
        Height = 17
        Caption = 'Robert Tilden Medley'
        TabOrder = 1
      end
      object Cand02: TRadioButton
        Left = 8
        Top = 56
        Width = 440
        Height = 17
        Caption = 'Warren E. Hanson'
        TabOrder = 2
      end
      object Cand03: TRadioButton
        Left = 8
        Top = 80
        Width = 441
        Height = 17
        Caption = 'Barbara Lampert'
        TabOrder = 3
      end
      object Cand04: TRadioButton
        Left = 8
        Top = 104
        Width = 441
        Height = 17
        Caption = 'Slade Gorton'
        TabOrder = 4
      end
      object Cand05: TRadioButton
        Left = 8
        Top = 128
        Width = 441
        Height = 17
        Caption = 'June Riggs'
        TabOrder = 5
      end
      object Cand06: TRadioButton
        Left = 8
        Top = 152
        Width = 441
        Height = 17
        Caption = 'Ken McCandless'
        TabOrder = 6
      end
      object Cand07: TRadioButton
        Left = 8
        Top = 176
        Width = 441
        Height = 17
        Caption = 'Deborah Senn'
        TabOrder = 7
      end
      object Cand08: TRadioButton
        Left = 8
        Top = 200
        Width = 441
        Height = 17
        Caption = 'Jeff Jared'
        TabOrder = 8
      end
      object Cand09: TRadioButton
        Left = 8
        Top = 344
        Width = 441
        Height = 17
        Caption = 'Abstain'
        Checked = True
        TabOrder = 9
        TabStop = True
      end
    end
    object TabSheet1: TTabSheet
      Caption = 'U.S. Representative Dist 1'
      ImageIndex = 1
      object Conf10: TStaticText
        Left = 456
        Top = 8
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 4
        Visible = False
      end
      object Conf11: TStaticText
        Left = 456
        Top = 32
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 5
        Visible = False
      end
      object Conf12: TStaticText
        Left = 456
        Top = 56
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 6
        Visible = False
      end
      object Conf13: TStaticText
        Left = 456
        Top = 344
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 7
        Visible = False
      end
      object Cand10: TRadioButton
        Left = 8
        Top = 8
        Width = 441
        Height = 17
        Caption = 'Dan McDonald'
        TabOrder = 0
      end
      object Cand11: TRadioButton
        Left = 8
        Top = 32
        Width = 441
        Height = 17
        Caption = 'Jay Inslee'
        TabOrder = 1
      end
      object Cand12: TRadioButton
        Left = 9
        Top = 56
        Width = 441
        Height = 17
        Caption = 'Bruce Newman'
        TabOrder = 2
      end
      object Cand13: TRadioButton
        Left = 8
        Top = 344
        Width = 441
        Height = 17
        Caption = 'Abstain'
        Checked = True
        TabOrder = 3
        TabStop = True
      end
    end
    object TabSheet2: TTabSheet
      Caption = 'Governor'
      ImageIndex = 2
      object Conf20: TStaticText
        Left = 456
        Top = 8
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 6
        Visible = False
      end
      object Conf21: TStaticText
        Left = 456
        Top = 32
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 7
        Visible = False
      end
      object Conf22: TStaticText
        Left = 456
        Top = 56
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 8
        Visible = False
      end
      object Conf23: TStaticText
        Left = 456
        Top = 80
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 9
        Visible = False
      end
      object Conf24: TStaticText
        Left = 456
        Top = 104
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 10
        Visible = False
      end
      object Conf25: TStaticText
        Left = 456
        Top = 344
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 11
        Visible = False
      end
      object Cand20: TRadioButton
        Left = 8
        Top = 8
        Width = 441
        Height = 17
        Caption = 'Gary Locke'
        TabOrder = 0
      end
      object Cand21: TRadioButton
        Left = 8
        Top = 32
        Width = 441
        Height = 17
        Caption = 'Harold Hockstatter'
        TabOrder = 1
      end
      object Cand22: TRadioButton
        Left = 9
        Top = 56
        Width = 441
        Height = 17
        Caption = 'Meta Heller'
        TabOrder = 2
      end
      object Cand23: TRadioButton
        Left = 9
        Top = 80
        Width = 441
        Height = 17
        Caption = 'Steve W. LePage'
        TabOrder = 3
      end
      object Cand24: TRadioButton
        Left = 9
        Top = 104
        Width = 441
        Height = 17
        Caption = 'John Carlson'
        TabOrder = 4
      end
      object Cand25: TRadioButton
        Left = 8
        Top = 344
        Width = 441
        Height = 17
        Caption = 'Abstain'
        Checked = True
        TabOrder = 5
        TabStop = True
      end
    end
    object TabSheet3: TTabSheet
      Caption = 'Lieutenant Governor'
      ImageIndex = 3
      object Conf30: TStaticText
        Left = 456
        Top = 8
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 6
        Visible = False
      end
      object Conf31: TStaticText
        Left = 456
        Top = 32
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 7
        Visible = False
      end
      object Conf32: TStaticText
        Left = 456
        Top = 56
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 8
        Visible = False
      end
      object Conf33: TStaticText
        Left = 456
        Top = 80
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 9
        Visible = False
      end
      object Conf34: TStaticText
        Left = 456
        Top = 104
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 10
        Visible = False
      end
      object Conf35: TStaticText
        Left = 456
        Top = 344
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 11
        Visible = False
      end
      object Cand30: TRadioButton
        Left = 9
        Top = 8
        Width = 441
        Height = 17
        Caption = 'Lonnie W. Williams, Sr.'
        TabOrder = 0
      end
      object Cand31: TRadioButton
        Left = 9
        Top = 32
        Width = 441
        Height = 17
        Caption = 'Brad Owen'
        TabOrder = 1
      end
      object Cand32: TRadioButton
        Left = 9
        Top = 56
        Width = 441
        Height = 17
        Caption = 'Joe E. Mitschelen'
        TabOrder = 2
      end
      object Cand33: TRadioButton
        Left = 9
        Top = 80
        Width = 441
        Height = 17
        Caption = 'Ruth E. Bennett'
        TabOrder = 3
      end
      object Cand34: TRadioButton
        Left = 9
        Top = 104
        Width = 441
        Height = 17
        Caption = 'Wm. (Mike) Elliott'
        TabOrder = 4
      end
      object Cand35: TRadioButton
        Left = 8
        Top = 344
        Width = 441
        Height = 17
        Caption = 'Abstain'
        Checked = True
        TabOrder = 5
        TabStop = True
      end
    end
    object TabSheet4: TTabSheet
      Caption = 'Secretary of State'
      ImageIndex = 4
      object Conf40: TStaticText
        Left = 456
        Top = 8
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 12
        Visible = False
      end
      object Conf41: TStaticText
        Left = 456
        Top = 32
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 13
        Visible = False
      end
      object Conf42: TStaticText
        Left = 456
        Top = 56
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 14
        Visible = False
      end
      object Conf43: TStaticText
        Left = 456
        Top = 80
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 15
        Visible = False
      end
      object Conf44: TStaticText
        Left = 456
        Top = 104
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 16
        Visible = False
      end
      object Conf45: TStaticText
        Left = 456
        Top = 128
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 17
        Visible = False
      end
      object Conf46: TStaticText
        Left = 456
        Top = 152
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 18
        Visible = False
      end
      object Conf47: TStaticText
        Left = 456
        Top = 176
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 19
        Visible = False
      end
      object Conf48: TStaticText
        Left = 456
        Top = 200
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 20
        Visible = False
      end
      object Conf49: TStaticText
        Left = 456
        Top = 224
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 21
        Visible = False
      end
      object Conf410: TStaticText
        Left = 456
        Top = 248
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 22
        Visible = False
      end
      object Conf411: TStaticText
        Left = 456
        Top = 344
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 23
        Visible = False
      end
      object Cand40: TRadioButton
        Left = 9
        Top = 8
        Width = 441
        Height = 17
        Caption = 'Chris Loftis'
        TabOrder = 0
      end
      object Cand41: TRadioButton
        Left = 9
        Top = 32
        Width = 441
        Height = 17
        Caption = 'Charles Rolland'
        TabOrder = 1
      end
      object Cand42: TRadioButton
        Left = 9
        Top = 56
        Width = 441
        Height = 17
        Caption = 'Don L. Bonker'
        TabOrder = 2
      end
      object Cand43: TRadioButton
        Left = 9
        Top = 80
        Width = 441
        Height = 17
        Caption = 'James Findley'
        TabOrder = 3
      end
      object Cand44: TRadioButton
        Left = 9
        Top = 104
        Width = 441
        Height = 17
        Caption = 'Sam Reed'
        TabOrder = 4
      end
      object Cand45: TRadioButton
        Left = 9
        Top = 128
        Width = 441
        Height = 17
        Caption = 'Allen Norman'
        TabOrder = 5
      end
      object Cand46: TRadioButton
        Left = 9
        Top = 152
        Width = 441
        Height = 17
        Caption = 'Mike Wensman'
        TabOrder = 6
      end
      object Cand47: TRadioButton
        Left = 9
        Top = 176
        Width = 441
        Height = 17
        Caption = 'J. Bradley Gibson'
        TabOrder = 7
      end
      object Cand48: TRadioButton
        Left = 9
        Top = 200
        Width = 441
        Height = 17
        Caption = 'Will Baker'
        TabOrder = 8
      end
      object Cand49: TRadioButton
        Left = 9
        Top = 224
        Width = 441
        Height = 17
        Caption = 'Rand Daley'
        TabOrder = 9
      end
      object Cand410: TRadioButton
        Left = 9
        Top = 248
        Width = 441
        Height = 17
        Caption = 'Bob Terwilliger'
        TabOrder = 10
      end
      object Cand411: TRadioButton
        Left = 8
        Top = 344
        Width = 441
        Height = 17
        Caption = 'Abstain'
        Checked = True
        TabOrder = 11
        TabStop = True
      end
    end
    object TabSheet5: TTabSheet
      Caption = 'Treasurer'
      ImageIndex = 5
      object Conf50: TStaticText
        Left = 456
        Top = 8
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 5
        Visible = False
      end
      object Conf51: TStaticText
        Left = 456
        Top = 32
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 6
        Visible = False
      end
      object Conf52: TStaticText
        Left = 456
        Top = 56
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 7
        Visible = False
      end
      object Conf53: TStaticText
        Left = 456
        Top = 80
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 8
        Visible = False
      end
      object Conf54: TStaticText
        Left = 456
        Top = 344
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 9
        Visible = False
      end
      object Cand50: TRadioButton
        Left = 9
        Top = 8
        Width = 441
        Height = 17
        Caption = 'Mike Murphy'
        TabOrder = 0
      end
      object Cand51: TRadioButton
        Left = 9
        Top = 32
        Width = 441
        Height = 17
        Caption = 'Louis Bloom'
        TabOrder = 1
      end
      object Cand52: TRadioButton
        Left = 9
        Top = 56
        Width = 441
        Height = 17
        Caption = 'Diane Rhoades'
        TabOrder = 2
      end
      object Cand53: TRadioButton
        Left = 9
        Top = 80
        Width = 441
        Height = 17
        Caption = 'Tim Perman'
        TabOrder = 3
      end
      object Cand54: TRadioButton
        Left = 8
        Top = 344
        Width = 441
        Height = 17
        Caption = 'Abstain'
        Checked = True
        TabOrder = 4
        TabStop = True
      end
    end
    object TabSheet6: TTabSheet
      Caption = 'Auditor'
      ImageIndex = 6
      object Conf60: TStaticText
        Left = 456
        Top = 8
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 4
        Visible = False
      end
      object Conf61: TStaticText
        Left = 456
        Top = 32
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 5
        Visible = False
      end
      object Conf62: TStaticText
        Left = 456
        Top = 56
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 6
        Visible = False
      end
      object Conf63: TStaticText
        Left = 456
        Top = 344
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 7
        Visible = False
      end
      object Cand60: TRadioButton
        Left = 9
        Top = 8
        Width = 441
        Height = 17
        Caption = 'Brian Sontag'
        TabOrder = 0
      end
      object Cand61: TRadioButton
        Left = 9
        Top = 32
        Width = 441
        Height = 17
        Caption = 'Chris Caputo'
        TabOrder = 1
      end
      object Cand62: TRadioButton
        Left = 9
        Top = 56
        Width = 441
        Height = 17
        Caption = 'Richard McEntee'
        TabOrder = 2
      end
      object Cand63: TRadioButton
        Left = 8
        Top = 344
        Width = 441
        Height = 17
        Caption = 'Abstain'
        Checked = True
        TabOrder = 3
        TabStop = True
      end
    end
    object TabSheet7: TTabSheet
      Caption = 'Attorney General'
      ImageIndex = 7
      object Conf70: TStaticText
        Left = 456
        Top = 8
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 6
        Visible = False
      end
      object Conf71: TStaticText
        Left = 456
        Top = 32
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 7
        Visible = False
      end
      object Conf72: TStaticText
        Left = 456
        Top = 56
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 8
        Visible = False
      end
      object Conf73: TStaticText
        Left = 456
        Top = 80
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 9
        Visible = False
      end
      object Conf74: TStaticText
        Left = 456
        Top = 104
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 10
        Visible = False
      end
      object Conf75: TStaticText
        Left = 456
        Top = 344
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 11
        Visible = False
      end
      object Cand70: TRadioButton
        Left = 9
        Top = 8
        Width = 441
        Height = 17
        Caption = 'Christine Gregoire'
        TabOrder = 0
      end
      object Cand71: TRadioButton
        Left = 9
        Top = 32
        Width = 441
        Height = 17
        Caption = 'Stan Lippman'
        TabOrder = 1
      end
      object Cand72: TRadioButton
        Left = 9
        Top = 56
        Width = 441
        Height = 17
        Caption = 'Luanne Coachman'
        TabOrder = 2
      end
      object Cand73: TRadioButton
        Left = 9
        Top = 80
        Width = 441
        Height = 17
        Caption = 'Richard Pope'
        TabOrder = 3
      end
      object Cand74: TRadioButton
        Left = 9
        Top = 104
        Width = 441
        Height = 17
        Caption = 'Richard Shepard'
        TabOrder = 4
      end
      object Cand75: TRadioButton
        Left = 8
        Top = 344
        Width = 441
        Height = 17
        Caption = 'Abstain'
        Checked = True
        TabOrder = 5
        TabStop = True
      end
    end
    object TabSheet8: TTabSheet
      Caption = 'Commissioner of Public Lands'
      ImageIndex = 8
      object Conf80: TStaticText
        Left = 456
        Top = 8
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 10
        Visible = False
      end
      object Conf81: TStaticText
        Left = 456
        Top = 32
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 11
        Visible = False
      end
      object Conf82: TStaticText
        Left = 456
        Top = 56
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 12
        Visible = False
      end
      object Conf83: TStaticText
        Left = 456
        Top = 80
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 13
        Visible = False
      end
      object Conf84: TStaticText
        Left = 456
        Top = 104
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 14
        Visible = False
      end
      object Conf85: TStaticText
        Left = 456
        Top = 128
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 15
        Visible = False
      end
      object Conf86: TStaticText
        Left = 456
        Top = 152
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 16
        Visible = False
      end
      object Conf87: TStaticText
        Left = 456
        Top = 176
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 17
        Visible = False
      end
      object Conf88: TStaticText
        Left = 456
        Top = 200
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 18
        Visible = False
      end
      object Conf89: TStaticText
        Left = 456
        Top = 344
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 19
        Visible = False
      end
      object Cand80: TRadioButton
        Left = 9
        Top = 8
        Width = 441
        Height = 17
        Caption = 'Georgia Gardner'
        TabOrder = 0
      end
      object Cand81: TRadioButton
        Left = 9
        Top = 32
        Width = 441
        Height = 17
        Caption = 'Steve Layman'
        TabOrder = 1
      end
      object Cand82: TRadioButton
        Left = 9
        Top = 56
        Width = 441
        Height = 17
        Caption = 'Patrick A. Parrish'
        TabOrder = 2
      end
      object Cand83: TRadioButton
        Left = 9
        Top = 80
        Width = 441
        Height = 17
        Caption = 'Bob Penhale'
        TabOrder = 3
      end
      object Cand84: TRadioButton
        Left = 9
        Top = 104
        Width = 441
        Height = 17
        Caption = 'Mike The Mover'
        TabOrder = 4
      end
      object Cand85: TRadioButton
        Left = 9
        Top = 128
        Width = 441
        Height = 17
        Caption = 'Mike Lowry'
        TabOrder = 5
      end
      object Cand86: TRadioButton
        Left = 9
        Top = 152
        Width = 441
        Height = 17
        Caption = 'Jim O'#39'Donnell'
        TabOrder = 6
      end
      object Cand87: TRadioButton
        Left = 9
        Top = 176
        Width = 441
        Height = 17
        Caption = 'Tim Reid'
        TabOrder = 7
      end
      object Cand88: TRadioButton
        Left = 9
        Top = 200
        Width = 441
        Height = 17
        Caption = 'Doug Sutherland'
        TabOrder = 8
      end
      object Cand89: TRadioButton
        Left = 8
        Top = 344
        Width = 441
        Height = 17
        Caption = 'Abstain'
        Checked = True
        TabOrder = 9
        TabStop = True
      end
    end
    object TabSheet9: TTabSheet
      Caption = 'Superintendent of Public Instruction'
      ImageIndex = 9
      object Conf90: TStaticText
        Left = 456
        Top = 8
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 6
        Visible = False
      end
      object Conf91: TStaticText
        Left = 456
        Top = 32
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 7
        Visible = False
      end
      object Conf92: TStaticText
        Left = 456
        Top = 56
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 8
        Visible = False
      end
      object Conf93: TStaticText
        Left = 456
        Top = 80
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 9
        Visible = False
      end
      object Conf94: TStaticText
        Left = 456
        Top = 104
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 10
        Visible = False
      end
      object Conf95: TStaticText
        Left = 456
        Top = 344
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 11
        Visible = False
      end
      object Cand91: TRadioButton
        Left = 9
        Top = 32
        Width = 441
        Height = 17
        Caption = 'Teresa Bergeson'
        TabOrder = 0
      end
      object Cand90: TRadioButton
        Left = 9
        Top = 8
        Width = 441
        Height = 17
        Caption = 'Arthur Hu'
        TabOrder = 1
      end
      object Cand92: TRadioButton
        Left = 9
        Top = 56
        Width = 441
        Height = 17
        Caption = 'David Blomstrom'
        TabOrder = 2
      end
      object Cand93: TRadioButton
        Left = 9
        Top = 80
        Width = 441
        Height = 17
        Caption = 'Donald B. Crawford'
        TabOrder = 3
      end
      object Cand94: TRadioButton
        Left = 9
        Top = 104
        Width = 441
        Height = 17
        Caption = 'Neil T.B. Helgeland'
        TabOrder = 4
      end
      object Cand95: TRadioButton
        Left = 8
        Top = 344
        Width = 441
        Height = 17
        Caption = 'Abstain'
        Checked = True
        TabOrder = 5
        TabStop = True
      end
    end
    object TabSheet10: TTabSheet
      Caption = 'Insurance Commissioner'
      ImageIndex = 10
      object Conf100: TStaticText
        Left = 456
        Top = 8
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 6
        Visible = False
      end
      object Conf101: TStaticText
        Left = 456
        Top = 32
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 7
        Visible = False
      end
      object Conf102: TStaticText
        Left = 456
        Top = 56
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 8
        Visible = False
      end
      object Conf103: TStaticText
        Left = 456
        Top = 80
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 9
        Visible = False
      end
      object Conf104: TStaticText
        Left = 456
        Top = 104
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 10
        Visible = False
      end
      object Conf105: TStaticText
        Left = 456
        Top = 344
        Width = 43
        Height = 26
        Caption = 'XXX'
        TabOrder = 11
        Visible = False
      end
      object Cand100: TRadioButton
        Left = 9
        Top = 8
        Width = 441
        Height = 17
        Caption = 'Mike Kreidler'
        TabOrder = 0
      end
      object Cand101: TRadioButton
        Left = 9
        Top = 32
        Width = 441
        Height = 17
        Caption = 'Don Davidson'
        TabOrder = 1
      end
      object Cand102: TRadioButton
        Left = 9
        Top = 56
        Width = 441
        Height = 17
        Caption = 'Curtis Fackler'
        TabOrder = 2
      end
      object Cand103: TRadioButton
        Left = 9
        Top = 80
        Width = 441
        Height = 17
        Caption = 'John Conniff'
        TabOrder = 3
      end
      object Cand104: TRadioButton
        Left = 9
        Top = 104
        Width = 441
        Height = 17
        Caption = 'Mike Hihn'
        TabOrder = 4
      end
      object Cand105: TRadioButton
        Left = 8
        Top = 344
        Width = 441
        Height = 17
        Caption = 'Abstain'
        Checked = True
        TabOrder = 5
        TabStop = True
      end
    end
    object Confirm: TTabSheet
      Caption = 'Confirm'
      ImageIndex = 11
      object Label1: TStaticText
        Left = 8
        Top = 8
        Width = 111
        Height = 26
        Caption = 'U.S. Senator'
        TabOrder = 12
      end
      object Label2: TStaticText
        Left = 8
        Top = 32
        Width = 227
        Height = 26
        Caption = 'U.S. Representative Dist 1'
        TabOrder = 13
      end
      object Label3: TStaticText
        Left = 8
        Top = 56
        Width = 83
        Height = 26
        Caption = 'Governor'
        TabOrder = 14
      end
      object Label4: TStaticText
        Left = 8
        Top = 80
        Width = 175
        Height = 26
        Caption = 'Lieutenant Governor'
        TabOrder = 15
      end
      object Label5: TStaticText
        Left = 8
        Top = 104
        Width = 156
        Height = 26
        Caption = 'Secretary of State'
        TabOrder = 16
      end
      object Label6: TStaticText
        Left = 8
        Top = 128
        Width = 86
        Height = 26
        Caption = 'Treasurer'
        TabOrder = 17
      end
      object Label7: TStaticText
        Left = 8
        Top = 152
        Width = 64
        Height = 26
        Caption = 'Auditor'
        TabOrder = 18
      end
      object Label8: TStaticText
        Left = 8
        Top = 176
        Width = 146
        Height = 26
        Caption = 'Attorney General'
        TabOrder = 19
      end
      object Label9: TStaticText
        Left = 8
        Top = 200
        Width = 263
        Height = 26
        Caption = 'Commissioner of Public Lands'
        TabOrder = 20
      end
      object Label10: TStaticText
        Left = 8
        Top = 224
        Width = 303
        Height = 26
        Caption = 'Superintendent of Public Instruction'
        TabOrder = 21
      end
      object Label11: TStaticText
        Left = 8
        Top = 248
        Width = 215
        Height = 26
        Caption = 'Insurance Commissioner'
        TabOrder = 22
      end
      object Cast: TButton
        Left = 360
        Top = 304
        Width = 137
        Height = 73
        Caption = 'Cast'
        TabOrder = 0
        OnClick = CastClick
      end
      object CD0: TStaticText
        Left = 336
        Top = 8
        Width = 30
        Height = 26
        Caption = 'XX'
        TabOrder = 1
      end
      object CD1: TStaticText
        Left = 336
        Top = 32
        Width = 30
        Height = 26
        Caption = 'XX'
        TabOrder = 2
      end
      object CD2: TStaticText
        Left = 336
        Top = 56
        Width = 30
        Height = 26
        Caption = 'XX'
        TabOrder = 3
      end
      object CD3: TStaticText
        Left = 336
        Top = 80
        Width = 30
        Height = 26
        Caption = 'XX'
        TabOrder = 4
      end
      object CD4: TStaticText
        Left = 336
        Top = 104
        Width = 30
        Height = 26
        Caption = 'XX'
        TabOrder = 5
      end
      object CD5: TStaticText
        Left = 336
        Top = 128
        Width = 30
        Height = 26
        Caption = 'XX'
        TabOrder = 6
      end
      object CD6: TStaticText
        Left = 336
        Top = 152
        Width = 30
        Height = 26
        Caption = 'XX'
        TabOrder = 7
      end
      object CD7: TStaticText
        Left = 336
        Top = 176
        Width = 30
        Height = 26
        Caption = 'XX'
        TabOrder = 8
      end
      object CD8: TStaticText
        Left = 336
        Top = 200
        Width = 30
        Height = 26
        Caption = 'XX'
        TabOrder = 9
      end
      object CD9: TStaticText
        Left = 336
        Top = 224
        Width = 30
        Height = 26
        Caption = 'XX'
        TabOrder = 10
      end
      object CD10: TStaticText
        Left = 336
        Top = 248
        Width = 30
        Height = 26
        Caption = 'XX'
        TabOrder = 11
      end
    end
  end
end
