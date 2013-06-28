(*  *)
(* This material is subject to the VoteHere Source Code Evaluation *)
(* License Agreement ("Agreement").  Possession and/or use of this *)
(* material indicates your acceptance of this Agreement in its entirety. *)
(* Copies of the Agreement may be found at www.votehere.net. *)
(*  *)
(* Copyright 2004 VoteHere, Inc.  All Rights Reserved *)
(*  *)
(* You may not download this Software if you are located in any country *)
(* (or are a national of a country) subject to a general U.S. or *)
(* U.N. embargo or are deemed to be a terrorist country (i.e., Cuba, *)
(* Iran, Iraq, Libya, North Korea, Sudan and Syria) by the United States *)
(* (each a "Prohibited Country") or are otherwise denied export *)
(* privileges from the United States or Canada ("Denied Person"). *)
(* Further, you may not transfer or re-export the Software to any such *)
(* country or Denied Person without a license or authorization from the *)
(* U.S. government.  By downloading the Software, you represent and *)
(* warrant that you are not a Denied Person, are not located in or a *)
(* national of a Prohibited Country, and will not export or re-export to *)
(* any Prohibited Country or Denied Party. *)
unit trustee_pre;

interface

uses
  Windows, Messages, SysUtils, Variants, Classes, Graphics, Controls, Forms,
  Dialogs, StdCtrls, Buttons;

type
  TTAction = Procedure(Sender : TObject) of object;
  TTrusteePreForm = class(TForm)
    Label1: TLabel;
    GenSecretShare: TCheckBox;
    showSecretShare: TBitBtn;
    GenBroadcastValues: TCheckBox;
    showBroadcast: TBitBtn;
    GenCommittment: TCheckBox;
    showCommit: TBitBtn;
    GenVVKey: TCheckBox;
    showVVKey: TBitBtn;
    GenVVCommittments: TCheckBox;
    showVVCommit: TBitBtn;
    GenPairwiseSecrets: TCheckBox;
    showPairwise: TBitBtn;
    trusteeID: TComboBox;
    Label2: TLabel;
    InstallVVKey: TCheckBox;
    procedure FormCreate(Sender: TObject);
    procedure trusteeIDChange(Sender: TObject);
    procedure showDataClick(Sender: TObject);
    procedure GenSecretShareClick(Sender: TObject);
    procedure GenBroadcastValuesClick(Sender: TObject);
    procedure GenPairwiseSecretsClick(Sender: TObject);
    procedure GenCommittmentClick(Sender: TObject);
    procedure GenVVKeyClick(Sender: TObject);
    procedure GenVVCommittmentsClick(Sender: TObject);
    procedure InstallVVKeyClick(Sender: TObject);
    procedure FormClose(Sender: TObject; var Action: TCloseAction);
  private
    { Private declarations }
    function TrusteePrefix : string;
  public
    { Public declarations }
    tid : integer;
    authorityInfo : string;
    updating : boolean;
    procedure UpdateState;
    procedure DoStep(Action : TTAction; Sender : TObject);
    (* The worker functions. *)
    procedure GenSecretShareWork(Sender: TObject);
    procedure GenBroadcastValuesWork(Sender: TObject);
    procedure GenPairwiseSecretsWork(Sender: TObject);
    procedure GenCommittmentWork(Sender: TObject);
    procedure GenVVKeyWork(Sender: TObject);
    procedure GenVVCommittmentsWork(Sender: TObject);
    procedure installVVKeyWork(Sender: TObject);
  end;

var
  TrusteePreForm: TTrusteePreForm;

implementation

uses demo_const, demo_topform, vhti, vh_support, xml_display, pre_election;

{$R *.dfm}

function TTrusteePreForm.TrusteePrefix : string;
begin
  TrusteePrefix := 'trustee_' + IntToStr(tid) + '_';
end;

procedure TTrusteePreForm.UpdateState;
var
  havePairwise : boolean;
  i : integer;
begin
  updating := true;

  (* The easy ones first: the 'show' buttons. *)
  SetEnabledForShow(showSecretShare);
  SetEnabledForShow(showBroadcast);
  SetEnabledForShow(showPairwise);
  SetEnabledForShow(showCommit);
  SetEnabledForShow(showVVKey);
  SetEnabledForShow(showVVCommit);

  (* Slightly harder: the 'done' status. *)
  SetCheckedForDone(GenSecretShare, demo_const.trustee(tid, secret_values));
  SetCheckedForDone(GenBroadcastValues, demo_const.trustee(tid, broadcast_values));
  SetCheckedForDone(GenPairwiseSecrets, demo_const.trustee(tid, pairwise_secret(tid)));
  SetCheckedForDone(GenCommittment, demo_const.keyshare_commitment(tid));
  SetCheckedForDone(GenVVKey, demo_const.trustee(tid, vv_key));
  SetCheckedForDone(GenVVCommittments, demo_const.vv_a_commits(tid));
  SetCheckedForDone(InstallVVKey, demo_const.voter(TrusteePrefix + vv_key));

  (* Finally, the enabled next steps. *)
  GenSecretShare.Enabled := not GenSecretShare.Checked;
  GenBroadcastValues.Enabled := TopForm.HasElectionString(demo_const.trustee(tid, secret_values))
      and not GenBroadcastValues.Checked;
  GenPairwiseSecrets.Enabled := TopForm.HasElectionString(
        demo_const.trustee(tid, broadcast_values))
      and TopForm.HasElectionString(demo_const.trustee(tid, authority))
      and not GenPairwiseSecrets.Checked;
  havePairwise := true;
  for i := 1 to TopForm.NumAuth do
  begin
    (* if i <> tid then *)
      havePairwise := havePairwise
          and TopForm.HasElectionString(demo_const.trustee(tid, pairwise_secret(i)));
  end;
  GenCommittment.Enabled := havePairwise
      and TopForm.HasElectionString(demo_const.trustee(tid, broadcast_values))
      and not GenCommittment.Checked;
  GenVVKey.Enabled := not GenVVKey.Checked;
  GenVVCommittments.Enabled := TopForm.HasElectionString(demo_const.a_bsns)
      and TopForm.HasElectionString(demo_const.trustee(tid, vv_key))
      and TopForm.HasElectionString(demo_const.blank_ballot)
      and not GenVVCommittments.Checked;
  InstallVVKey.Enabled := TopForm.HasElectionString(demo_const.trustee(tid, vv_key))
      and not InstallVVKey.Checked;

  updating := false;
end;

procedure TTrusteePreForm.DoStep(Action : TTAction; Sender : TObject);
begin
  if not updating then
  begin
    Screen.Cursor := crHourGlass;
    Action(Sender);
    Screen.Cursor := crDefault;
    TopForm.UpdateState;
  end;
end;

procedure TTrusteePreForm.FormCreate(Sender: TObject);
begin
  updating := true;
  showSecretShare.Hint := demo_const.trustee(tid, secret_values);
  showBroadcast.Hint := demo_const.trustee(tid, broadcast_values);
  showPairwise.Hint := demo_const.trustee(tid, pairwise_secret(tid));
  showCommit.Hint := demo_const.keyshare_commitment(tid);
  showVVKey.Hint := demo_const.trustee(tid, vv_key);
  showVVCommit.Hint := demo_const.vv_a_commits(tid);
  updating := false;
end;

procedure TTrusteePreForm.showDataClick(Sender: TObject);
begin
  XmlDisplay.ShowFile(TControl(Sender).Hint);
end;

procedure TTrusteePreForm.trusteeIDChange(Sender: TObject);
begin
  (* A cheezy way to get the various fields set right. *)
  Screen.Cursor := crHourGlass;
  tid := trusteeID.ItemIndex + 1;
  authorityInfo := TopForm.GetElectionString(demo_const.trustee(tid, authority));

  FormCreate(self);

  Screen.Cursor := crDefault;
  TopForm.UpdateState;
end;

procedure TTrusteePreForm.GenSecretShareWork(Sender: TObject);
var
  randomState : string;
  secretCoefficients : string;
begin
  randomState := TopForm.GetElectionString(demo_const.random_state);
  vhti.generate_secret_coefficients(
      TopForm.GetElectionString(demo_const.keygen_params),
      authorityInfo, randomState, secretCoefficients, randomState);
  TopForm.SetElectionString(demo_const.trustee(tid, secret_values), secretCoefficients);
  TopForm.SetElectionString(demo_const.random_state, randomState);
end;

procedure TTrusteePreForm.GenBroadcastValuesWork(Sender: TObject);
var
  randomState : string;
  broadcastValue : string;
begin
  randomState := TopForm.GetElectionString(demo_const.random_state);
  vhti.generate_broadcast(TopForm.GetElectionString(demo_const.keygen_params),
      TopForm.GetElectionString(demo_const.trustee(tid, secret_values)),
      randomState, broadcastValue, randomState);
  TopForm.SetElectionString(demo_const.trustee(tid, broadcast_values), broadcastValue);
  TopForm.SetElectionString(demo_const.random_state, randomState);
end;

procedure TTrusteePreForm.GenPairwiseSecretsWork(Sender: TObject);
var
  i : integer;
  secret : string;
begin
  for i := 1 to TopForm.NumAuth do
  begin
    vhti.generate_secret(TopForm.GetElectionString(demo_const.keygen_params),
        TopForm.GetElectionString(demo_const.trustee(i, authority)),
        TopForm.GetElectionString(demo_const.trustee(tid, secret_values)),
        secret);
    TopForm.SetElectionString(demo_const.trustee(i,
        demo_const.pairwise_secret(tid)), secret);
  end;
end;

procedure TTrusteePreForm.GenCommittmentWork(Sender: TObject);
var
  i : integer;
  keygenParams : string;
  broadcasts : string;
  pairSecrets : string;
  secretShare : string;
  keyshareCommit : string;
begin
  broadcasts := '';
  pairSecrets := '';

  for i := 1 to TopForm.NumAuth do
  begin
    broadcasts := broadcasts +
        TopForm.GetElectionString(demo_const.trustee(i, broadcast_values));
    pairSecrets := pairSecrets +
        TopForm.GetElectionString(demo_const.trustee(tid, pairwise_secret(i)));
  end;

  keygenParams := TopForm.GetElectionString(demo_const.keygen_params);
  broadcasts := demo_const.xml_element('BroadcastValues', '', broadcasts);
  pairSecrets := demo_const.xml_element('PairwiseSecrets', '', pairSecrets);

  TopForm.SetElectionString('t_keygen_params.xml', keygenParams);
  TopForm.SetElectionString('t_authority_info.xml', authorityInfo);
  TopForm.SetElectionString('t_broadcasts.xml', broadcasts);
  TopForm.SetElectionString('t_pair_secrets.xml', pairSecrets);

  vhti.generate_commitment(keygenParams, authorityInfo, broadcasts,
      pairSecrets, secretShare, keyshareCommit);

  TopForm.SetElectionString(demo_const.trustee(tid, secret_share), secretShare);
  TopForm.SetElectionString(demo_const.keyshare_commitment(tid), keyshareCommit);
end;

procedure TTrusteePreForm.GenVVKeyWork(Sender: TObject);
var
  randomState : string;
  vvkey : string;
begin
  randomState := TopForm.GetElectionString(demo_const.random_state);
  vhti.generate_vvk(randomState, vvkey, randomState);
  TopForm.SetElectionString(demo_const.random_state, randomState);
  TopForm.SetElectionString(demo_const.trustee(tid, vv_key), vvkey);
end;

procedure TTrusteePreForm.GenVVCommittmentsWork(Sender: TObject);
var
  vvcomm : string;
begin
  vhti.generate_vvdict_commits(authorityInfo,
      TopForm.GetElectionString(demo_const.trustee(tid, prv_key)),
      TopForm.GetElectionString(demo_const.trustee(tid, vv_key)),
      TopForm.GetElectionString(demo_const.blank_ballot),
      TopForm.GetElectionString(demo_const.a_bsns),
      vvcomm);
  TopForm.SetElectionString(demo_const.vv_a_commits(tid), vvcomm);
  vhti.generate_vvdict_commits(authorityInfo,
      TopForm.GetElectionString(demo_const.trustee(tid, prv_key)),
      TopForm.GetElectionString(demo_const.trustee(tid, vv_key)),
      TopForm.GetElectionString(demo_const.blank_ballot),
      TopForm.GetElectionString(demo_const.p_bsns),
      vvcomm);
  TopForm.SetElectionString(demo_const.vv_p_commits(tid), vvcomm);
end;

procedure TTrusteePreForm.installVVKeyWork(Sender: TObject);
begin
  TopForm.SetElectionString(demo_const.voter(TrusteePrefix + vv_key),
      TopForm.GetElectionString(demo_const.trustee(TrusteePreForm.tid, vv_key)));
end;

procedure TTrusteePreForm.GenSecretShareClick(Sender: TObject);
begin
  DoStep(GenSecretShareWork, Sender);
end;

procedure TTrusteePreForm.GenBroadcastValuesClick(Sender: TObject);
begin
  DoStep(GenBroadcastValuesWork, Sender);
end;

procedure TTrusteePreForm.GenPairwiseSecretsClick(Sender: TObject);
begin
  DoStep(GenPairwiseSecretsWork, Sender);
end;

procedure TTrusteePreForm.GenCommittmentClick(Sender: TObject);
begin
  DoStep(GenCommittmentWork, Sender);
end;

procedure TTrusteePreForm.GenVVKeyClick(Sender: TObject);
begin
  DoStep(GenVVKeyWork, Sender);
end;

procedure TTrusteePreForm.GenVVCommittmentsClick(Sender: TObject);
begin
  DoStep(GenVVCommittmentsWork, Sender);
end;

procedure TTrusteePreForm.installVVKeyClick(Sender: TObject);
begin
  DoStep(installVVKeyWork, Sender);
end;

procedure TTrusteePreForm.FormClose(Sender: TObject;
  var Action: TCloseAction);
begin
  PreElectionForm.Visible := true;
end;

end.
