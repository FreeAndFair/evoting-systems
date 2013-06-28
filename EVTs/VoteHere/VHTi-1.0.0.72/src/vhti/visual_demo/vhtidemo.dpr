program vhtidemo;

uses
  Forms,
  demo_topform in 'demo_topform.pas' {TopForm},
  open_election in 'open_election.pas' {OpenElectionFrm},
  vh_support in 'vh_support.pas',
  demo_const in 'demo_const.pas',
  election_phases in 'election_phases.pas' {ElectionPhasesForm},
  pre_election in 'pre_election.pas' {PreElectionForm},
  leo_pre in 'leo_pre.pas' {LeoPreElectionForm},
  seed_params in 'seed_params.pas' {SeedParametersForm},
  ident_info in 'ident_info.pas' {IdentInfo},
  new_election in 'new_election.pas' {NewElectionForm},
  trustee_pre in 'trustee_pre.pas' {TrusteePreForm},
  ballot_skeleton in 'ballot_skeleton.pas' {ballotSkeleton},
  create_bsn in 'create_bsn.pas' {CreateBSNsForm},
  trans_election in 'trans_election.pas' {TransElectionForm},
  pollworker_trans in 'pollworker_trans.pas' {PollworkerTransForm},
  voter_trans in 'voter_trans.pas' {VoterTransForm},
  xml_display in 'xml_display.pas' {XmlDisplay},
  voter_preconfig in 'voter_preconfig.pas' {VoterInterfacePreconfig},
  voter_custom in 'voter_custom.pas' {VoterInterfaceCustom},
  virtual_printer in 'virtual_printer.pas' {PrinterOutput},
  leo_post in 'leo_post.pas' {LeoPostElectionForm},
  trustee_post in 'trustee_post.pas' {TrusteePostForm},
  post_election in 'post_election.pas' {PostElectionForm},
  vhti in '..\..\..\..\development\src\vhti\bindings\delphi\vhti.pas';

{$R *.res}

begin
  Randomize;
  Application.Initialize;
  Application.Title := 'VHTi Visual Demo';
  Application.CreateForm(TTopForm, TopForm);
  Application.CreateForm(TOpenElectionFrm, OpenElectionFrm);
  Application.CreateForm(TElectionPhasesForm, ElectionPhasesForm);
  Application.CreateForm(TPreElectionForm, PreElectionForm);
  Application.CreateForm(TLeoPreElectionForm, LeoPreElectionForm);
  Application.CreateForm(TSeedParametersForm, SeedParametersForm);
  Application.CreateForm(TIdentInfo, IdentInfo);
  Application.CreateForm(TNewElectionForm, NewElectionForm);
  Application.CreateForm(TTrusteePreForm, TrusteePreForm);
  Application.CreateForm(TballotSkeleton, ballotSkeleton);
  Application.CreateForm(TCreateBSNsForm, CreateBSNsForm);
  Application.CreateForm(TTransElectionForm, TransElectionForm);
  Application.CreateForm(TPollworkerTransForm, PollworkerTransForm);
  Application.CreateForm(TVoterTransForm, VoterTransForm);
  Application.CreateForm(TXmlDisplay, XmlDisplay);
  Application.CreateForm(TVoterInterfacePreconfig, VoterInterfacePreconfig);
  Application.CreateForm(TVoterInterfaceCustom, VoterInterfaceCustom);
  Application.CreateForm(TPrinterOutput, PrinterOutput);
  Application.CreateForm(TLeoPostElectionForm, LeoPostElectionForm);
  Application.CreateForm(TTrusteePostForm, TrusteePostForm);
  Application.CreateForm(TPostElectionForm, PostElectionForm);
  Application.Run;
end.
