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
unit demo_const;

interface

const
  path_sep = '\';
  xml = '.xml';
  txt = '.txt';

  election_config = 'election_config' + xml;
  random_state = 'random_state' + xml;
  threshold = 'threshold' + txt;
  num_auth = 'num_auth' + txt;
  keygen_params = 'keygen_params' + xml;
  leo_pub_key = 'leo_public_key' + xml;
  leo_prv_key = 'leo_private_key' + xml;
  ballot_skeleton = 'ballot_skeleton' + xml;
  election_pub_key = 'election_public_key' + xml;
  keyshare_commitment_prefix = 'keyshare_commitment_from_';
  vv_a_commits_prefix = 'voter_verification_authorized_commitments_from_';
  vv_p_commits_prefix = 'voter_verification_provisional_commitments_from_';
  cep = 'crypto_election_parameters' + xml;
  blank_ballot = 'blank_ballot' + xml;
  signed_blank_ballot = 'signed_blank_ballot' + xml;
  a_bsns = 'authorized_ballot_sequence_numbers' + xml;
  p_bsns = 'provisional_ballot_sequence_numbers' + xml;
  voter_roll = 'voter_roll' + xml;
  encoding = 'encoding' + xml;
  signed_voted_ballots = 'signed_voted_ballots' + xml;
  raw_ballot_box = 'raw_ballot_box' + xml;
  raw_ballot_box_latest = 'raw_ballot_box_latest' + xml;
  raw_ballot_box_before_prefix = 'raw_ballot_box_before_';
  raw_ballot_box_after_prefix = 'raw_ballot_box_after_';
  shuffle_validity_proof_prefix = 'shuffle_validity_proof_after_';
  shuffle_validity_proofs = 'shuffle_validity_proofs' + xml;
  clear_text_ballots = 'clear_text_ballots' + xml;
  election_results = 'election_results' + xml;
  verification_statements = 'verification_statements' + xml;
  pre_verification_code_box_prefix = 'pre_vcode_box_from_';
  pre_verification_code_boxes = 'pre_vcode_boxes' + xml;
  auth_partial_decrypt_prefix = 'auth_partial_decrypt_from_';
  auth_partial_decrypt4vcodes_prefix = 'auth_partial_decrypt4vcodes_from_';
  auth_partial_decrypts4vcodes = 'auth_partial_decrypts4vcodes' + xml;
  combine_partial_decrypt_result = 'combine_partial_decrypt_result' + xml;
  revealed_dictionary_secrets_prefix = 'revealed_dictionary_secrets_from_';
  revealed_dictionary_secrets_check_results_prefix =
     'revealed_dictionary_secrets_check_results_from_';
  trustee_revealed_dictionary_secrets_box =
    'trustee_revealed_dictionary_secrets_box' + xml;
  revealed_vote_verification_dictionaries =
    'revealed_vote_verification_dictionaries' + xml;

  trustee_dir_prefix = 'trustee_';
  authority = 'authority' + xml;
  committed_authority = 'committed_authority' + xml;
  secret_values = 'secret_values' + xml;
  broadcast_values = 'broadcast_values' + xml;
  pairwise_secrets = 'pairwise_secrets' + xml;
  pairwise_secret_prefix = 'secret_from_';
  secret_share = 'secret_share' + xml;
  vv_key = 'voter_verification_key' + xml;
  pub_key = 'public_key' + xml;
  prv_key = 'private_key' + xml;

  voter_dir = 'voter_data';
  (* The 'ballot_box' is not xml because it contains a list of signed
     voted ballots.  Wrapping a <SignedVotedBallots> around it makes it
     xml again. *)
  ballot_box = 'ballot_box' + txt;
  vv_keys = 'voter_verification_keys' + xml;
  assigned_bsn = 'assigned_bsn' + xml;
  verification_codes = 'verification_codes' + xml;
  unconfirmed_signed_voted_ballot = 'unconfirmed_signed_voted_ballot' + xml;
  receipt_data = 'receipt_data' + xml;
  signed_receipt = 'signed_receipt' + xml;
  { TODO -oandrewb : track down some nicer values for the numbits and the alphabet encoding }
  vvcode_numbits = 9;

  pollworker_dir = 'pollworker_data';
  polls_opened = 'polls_opened' + xml;
  polls_closed = 'polls_closed' + xml;

  eid = '1234';
  pid = '4321';

  xml_suffix = xml;

  function alphabet_encoding : string;
  function pairwise_secret(from : integer) : string;
  function trustee(num : integer; key : string) : string;
  function voter(key : string) : string;
  function pollworker(key : string) : string;
  function keyshare_commitment(from : integer) : string;
  function vv_a_commits(from : integer) : string;
  function vv_p_commits(from : integer) : string;
  function default_ballot_skeleton : string;
  function raw_ballot_box_before(from : integer) : string;
  function raw_ballot_box_after(from : integer) : string;
  function shuffle_validity_proof(from : integer) : string;
  function auth_partial_decrypt(from : integer) : string;
  function pre_verification_code_box(from : integer) : string;
  function auth_partial_decrypt4vcodes(from : integer) : string;
  function revealed_dictionary_secrets(from : integer) : string;
  function revealed_dictionary_secrets_check_results(from : integer) : string;
  function xml_entitify(content : string) : string;
  function xml_element(name : string; attr : string; content : string) : string;
    overload;
  function xml_element(name : string; attr : string; content : integer) : string;
    overload;
  function xml_attr(name : string; value : string) : string;
    overload;
  function xml_attr(name : string; value : integer) : string;
    overload;

implementation

uses
  sysutils;

function alphabet_encoding : string;
begin
  alphabet_encoding := xml_element('AlphabetEncoding', '', 'DEC');
end;

function pairwise_secret(from : integer) : string;
begin
  pairwise_secret := pairwise_secret_prefix + IntToStr(from) + xml_suffix;
end;

function trustee(num : integer; key : string) : string;
begin
  trustee := trustee_dir_prefix + IntToStr(num) + path_sep + key;
end;

function voter(key : string) : string;
begin
  voter := voter_dir + path_sep + key;
end;

function pollworker(key : string) : string;
begin
  pollworker := pollworker_dir + path_sep + key;
end;

function keyshare_commitment(from : integer) : string;
begin
  keyshare_commitment := keyshare_commitment_prefix + IntToStr(from) +
    xml_suffix;
end;

function vv_a_commits(from : integer) : string;
begin
  vv_a_commits := vv_a_commits_prefix + IntToStr(from) +
    xml_suffix;
end;

function vv_p_commits(from : integer) : string;
begin
  vv_p_commits := vv_p_commits_prefix + IntToStr(from) +
    xml_suffix;
end;

function default_ballot_skeleton : string;
  function AnsSkel(TextStructure : string) : string;
  begin
    AnsSkel := xml_element('AnswerSkeleton', '',
        xml_element('AnswerTextStructure', '', TextStructure))
        + #13#10;
  end;
begin
  default_ballot_skeleton := '<BallotSkeleton>'#13#10
    + xml_element('ElectionID', '', eid)
    + xml_element('PrecinctID', '', pid)
    + '<QuestionSkeleton>'#13#10
    + '<QuestionTextStructure>U.S. SENATOR</QuestionTextStructure>'#13#10
    + AnsSkel('Maria Cantwell')
    + AnsSkel('Robert Tilden Medley')
    + AnsSkel('Warren E. Hanson')
    + AnsSkel('Barbara Lampert')
    + AnsSkel('Slade Gorton')
    + AnsSkel('June Riggs')
    + AnsSkel('Ken McCandless')
    + AnsSkel('Deborah Senn')
    + AnsSkel('Jeff Jared')
    + AnsSkel('Abstain')
(*    + AnsSkel('Write In') *)
    + '</QuestionSkeleton>'#13#10
    + ''#13#10
    + '<QuestionSkeleton>'#13#10
    + '<QuestionTextStructure>U.S. REPRESENTATIVE DIST 1</QuestionTextStructure>'#13#10
    + AnsSkel('Dan McDonald')
    + AnsSkel('Jay Inslee')
    + AnsSkel('Bruce Newman')
    + AnsSkel('Abstain')
(*    + AnsSkel('Write In') *)
    + '</QuestionSkeleton>'#13#10
    + ''#13#10
    + '<QuestionSkeleton>'#13#10
    + '<QuestionTextStructure>GOVERNOR</QuestionTextStructure>'#13#10
    + AnsSkel('Gary Locke')
    + AnsSkel('Harold Hockstatter')
    + AnsSkel('Meta Heller')
    + AnsSkel('Steve W. LePage')
    + AnsSkel('John Carlson')
    + AnsSkel('Abstain')
(*    + AnsSkel('Write In') *)
    + '</QuestionSkeleton>'#13#10
    + ''#13#10
    + '<QuestionSkeleton>'#13#10
    + '<QuestionTextStructure>LIEUTENANT GOVERNOR</QuestionTextStructure>'#13#10
    + AnsSkel('Lonnie W. Williams, Sr.')
    + AnsSkel('Brad Owen')
    + AnsSkel('Joe E. Mitschelen')
    + AnsSkel('Ruth E. Bennett')
    + AnsSkel('Wm. (Mike) Elliott')
    + AnsSkel('Abstain')
(*    + AnsSkel('Write In') *)
    + '</QuestionSkeleton>'#13#10
    + ''#13#10
    + '<QuestionSkeleton>'#13#10
    + '<QuestionTextStructure>SECRETARY OF STATE</QuestionTextStructure>'#13#10
    + AnsSkel('Chris Loftis')
    + AnsSkel('Charles Rolland')
    + AnsSkel('Don L. Bonker')
    + AnsSkel('James Findley')
    + AnsSkel('Sam Reed')
    + AnsSkel('Allen Norman')
    + AnsSkel('Mike Wensman')
    + AnsSkel('J. Bradley Gibson')
    + AnsSkel('Will Baker')
    + AnsSkel('Rand Daley')
    + AnsSkel('Bob Terwilliger')
    + AnsSkel('Abstain')
(*    + AnsSkel('Write In') *)
    + '</QuestionSkeleton>'#13#10
    + ''#13#10
    + '<QuestionSkeleton>'#13#10
    + '<QuestionTextStructure>TREASURER</QuestionTextStructure>'#13#10
    + AnsSkel('Mike Murphy')
    + AnsSkel('Louis Bloom')
    + AnsSkel('Diane Rhoades')
    + AnsSkel('Tim Perman')
    + AnsSkel('Abstain')
(*    + AnsSkel('Write In') *)
    + '</QuestionSkeleton>'#13#10
    + ''#13#10
    + '<QuestionSkeleton>'#13#10
    + '<QuestionTextStructure>AUDITOR</QuestionTextStructure>'#13#10
    + AnsSkel('Brian Sontag')
    + AnsSkel('Chris Caputo')
    + AnsSkel('Richard McEntee')
    + AnsSkel('Abstain')
(*    + AnsSkel('Write In') *)
    + '</QuestionSkeleton>'#13#10
    + ''#13#10
    + '<QuestionSkeleton>'#13#10
    + '<QuestionTextStructure>ATTORNEY GENERAL</QuestionTextStructure>'#13#10
    + AnsSkel('Christine Gregoire')
    + AnsSkel('Stan Lippman')
    + AnsSkel('Luanne Coachman')
    + AnsSkel('Richard Pope')
    + AnsSkel('Richard Shepard')
    + AnsSkel('Abstain')
(*    + AnsSkel('Write In') *)
    + '</QuestionSkeleton>'#13#10
    + ''#13#10
    + '<QuestionSkeleton>'#13#10
    + '<QuestionTextStructure>COMMISSIONER OF PUBLIC LANDS</QuestionTextStructure>'#13#10
    + AnsSkel('Georgia Gardner')
    + AnsSkel('Steve Layman')
    + AnsSkel('Patrick A. Parrish')
    + AnsSkel('Bob Penhale')
    + AnsSkel('Mike The Mover')
    + AnsSkel('Mike Lowry')
    + AnsSkel('Jim O''Donnell')
    + AnsSkel('Tim Reid')
    + AnsSkel('Doug Sutherland')
    + AnsSkel('Abstain')
(*    + AnsSkel('Write In') *)
    + '</QuestionSkeleton>'#13#10
    + ''#13#10
    + '<QuestionSkeleton>'#13#10
    + '<QuestionTextStructure>SUPERINTENDENT OF PUBLIC INSTRUCTION</QuestionTextStructure>'#13#10
    + AnsSkel('Arthur Hu')
    + AnsSkel('Teresa Bergeson')
    + AnsSkel('David Blomstrom')
    + AnsSkel('Donald B. Crawford')
    + AnsSkel('Neil T.B. Helgeland')
    + AnsSkel('Abstain')
(*    + AnsSkel('Write In') *)
    + '</QuestionSkeleton>'#13#10
    + ''#13#10
    + '<QuestionSkeleton>'#13#10
    + '<QuestionTextStructure>INSURANCE COMMISSIONER</QuestionTextStructure>'#13#10
    + AnsSkel('Mike Kreidler')
    + AnsSkel('Don Davidson')
    + AnsSkel('Curtis Fackler')
    + AnsSkel('John Conniff')
    + AnsSkel('Mike Hihn')
    + AnsSkel('Abstain')
(*    + AnsSkel('Write In') *)
    + '</QuestionSkeleton>'#13#10
    + '<BallotTextStructure>Vote loudly!</BallotTextStructure>'#13#10
    + '</BallotSkeleton>'#13#10;
end;

function raw_ballot_box_before(from : integer) : string;
begin
  raw_ballot_box_before := raw_ballot_box_before_prefix +
     IntToStr(from) + xml_suffix;
end;

function raw_ballot_box_after(from : integer) : string;
begin
  raw_ballot_box_after := raw_ballot_box_after_prefix +
     IntToStr(from) + xml_suffix;
end;

function shuffle_validity_proof(from : integer) : string;
begin
  shuffle_validity_proof := shuffle_validity_proof_prefix +
     IntToStr(from) + xml_suffix;
end;

function auth_partial_decrypt(from : integer) : string;
begin
  auth_partial_decrypt := auth_partial_decrypt_prefix +
     IntToStr(from) + xml_suffix;
end;

function pre_verification_code_box(from : integer) : string;
begin
  pre_verification_code_box := pre_verification_code_box_prefix +
     IntToStr(from) + xml_suffix;
end;

function auth_partial_decrypt4vcodes(from : integer) : string;
begin
  auth_partial_decrypt4vcodes := auth_partial_decrypt4vcodes_prefix +
     IntToStr(from) + xml_suffix;
end;

function revealed_dictionary_secrets(from : integer) : string;
begin
  revealed_dictionary_secrets := revealed_dictionary_secrets_prefix +
     IntToStr(from) + xml_suffix;
end;

function revealed_dictionary_secrets_check_results(from : integer) : string;
begin
  revealed_dictionary_secrets_check_results :=
    revealed_dictionary_secrets_check_results_prefix + IntToStr(from) +
    xml_suffix;
end;

function xml_entitify(content : string) : string;
var
  entitified : string;
  i : integer;
begin
  entitified := '';
  for i := 1 to length(content) do
  begin
    case content[i] of
    '&' : entitified := entitified + '&amp;';
    '<' : entitified := entitified + '&lt;';
    '>' : entitified := entitified + '&gt;';
    else entitified := entitified + content[i];
    end;
  end;
  xml_entitify := entitified;
end;


function xml_element(name : string; attr : string; content : string) : string;
begin
  xml_element := '<' + name + attr + '>' + content + '</' + name + '>';
end;

function xml_element(name : string; attr : string; content : integer) : string;
begin
  xml_element := '<' + name + attr + '>' + IntToStr(content) + '</' + name + '>';
end;

function xml_attr(name : string; value : string) : string;
begin
  xml_attr := ' ' + name + '="' + value + '"';
end;

function xml_attr(name : string; value : integer) : string;
begin
  xml_attr := ' ' + name + '="' + IntToStr(value) + '"';
end;

end.
