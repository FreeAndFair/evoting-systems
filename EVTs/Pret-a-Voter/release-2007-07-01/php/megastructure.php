<?php

include_once("fieldclass4.php");
/** Megastucture array
  * This holds an array of all the tables, indexed by tablename, 
  *   and includes all the field names, types, and information 
  *   about the structure of the whole table group. 
  */

/** field types:
  *  key          (key of this table)
  *  num          (number of some kind)
  *  string       (short string)
  *  text         (long string)
  *  blob         (binary)
  */

// Field($type,$colDesc)

$megastructure = array();

/*  --------------------------------------------- AUDITMACHINES ----- */
$name = "auditmachine";
$megastructure[$name."s"] = array(
	$name."_id" => 			new Field("key",	"Auditmachine ID"),
	$name."_name" => 		new Field("string",	"Auditmachine Name"),
	$name."_publickey" => 		new Field("blob",	"Auditmachine Public key")  );


/*  --------------------------------------------- BALLOTFORMAUDITS ----- */
$name = "ballotformaudit";
$megastructure[$name."s"] = array(
	"ballotform_serialno" => 	new Field("key",	"Ballotform Serial Number"),
	"teller_id" => 			new Field("num",	"Teller ID"),
	"teller_batch" => 		new Field("num",	"Teller Batch"),
	"audit_germ" =>			new Field("blob",	"Audit Germ"),
	"audit_onion" => 		new Field("blob",	"Audit Onion"),
	"audit_permutation" => 		new Field("blob",	"Audit Permutation"),
	"audit_plaintext_permutation" => new Field("string",	"Audit Permutation String")   );
$megastructure[$name."s"]["teller_id"]->set("keyOfTable","tellers");



/*  --------------------------------------------- BALLOTFORMPAPERS ----- */
$name = "ballotformpaper";
$megastructure[$name."s"] = array(
	$name."_id" => 			new Field("key",	"Ballot form paper ID"),
	$name."_hash" => 		new Field("blob",	"Ballot form paper Hash"),
	$name."_status" => 		new Field("string",	"Ballot form paper Status"),
	$name."_statuschangedate" => 	new Field("string",	"Ballot form paper Status Change Date"),
	$name."_plaintext_hash" => 	new Field("string",	"Ballot form paper Pretty Hash"),
	"vote_object" => 		new Field("blob",	"Ballot form paper Vote Object"),
	"receipt_object" => 		new Field("blob",	"Ballot form paper Receipt Object") //,
//mk2	$name."_vote" => 		new Field("string",	"Ballot form paper Vote string"),
//mk2	$name."_signature" => 		new Field("blob",	"Ballot form paper Signature")  
	);



/*  --------------------------------------------- BALLOTFORMS ----- */
$name = "ballotform";
$megastructure[$name."s"] = array(
	$name."_serialno" => 		new Field("key",	"Ballotform Serial Number"),
	$name."_status" => 		new Field("string",	"Ballot form paper Hash"),
	"election_id" => 		new Field("num",	"Ballot form paper Signature"),
	"race_id" => 			new Field("num",	"Ballot form paper Signature"),
	"booth_id" => 			new Field("num",	"Ballot form paper Signature"),
	$name."_object" => 		new Field("blob",	"Ballot form paper Signature"),
	$name."_plaintext_vote" => 	new Field("string",	"Ballot form plaintext vote"),
	$name."_statuschangedate" => 	new Field("string",	"Ballot form paper Signature")  );
$megastructure[$name."s"]["election_id"]->set("keyOfTable","elections");
$megastructure[$name."s"]["race_id"]->set("keyOfTable","races");
$megastructure[$name."s"]["booth_id"]->set("keyOfTable","booths");



/*  --------------------------------------------- BALLOTFORMSINPAPERS ----- */
$name = "ballotform";
$megastructure[$name."sinpapers"] = array(
	$name."paper_id" => 		new Field("key",	"Ballot form paper ID"),
	$name."_id" => 			new Field("num",	"Ballot form ID"),
	"position" => 			new Field("num",	"Position (ballotformsinpapers)")  );
$megastructure[$name."sinpapers"]["ballotform_id"]->set("keyOfTable","ballotforms");


/*  --------------------------------------------- BOOTHS ----- */
$name = "booth";
$megastructure[$name."s"] = array(
	$name."_id" => 			new Field("key",	"Booth ID"),
	$name."_name" => 		new Field("string",	"Booth Name"),
	$name."_publickey" => 		new Field("blob",	"Booth Publickey")  );



/*  --------------------------------------------- CANDIDATERACES ----- */
$name = "candidate";
$megastructure[$name."races"] = array(
	"election_id" => 		new Field("key",	"Election ID"),
	"race_id" => 			new Field("num",	"Race ID"),
	"candidate_id" => 		new Field("num",	"Candidate ID")  );
$megastructure[$name."races"]["election_id"]->set("keyOfTable","elections");
$megastructure[$name."races"]["race_id"]->set("keyOfTable","races");
$megastructure[$name."races"]["candidate_id"]->set("keyOfTable","candidates");



/*  --------------------------------------------- CANDIDATES ----- */
$name = "candidate";
$megastructure[$name."s"] = array(
	$name."_id" => 			new Field("key",	"Candidate ID"),
	$name."_name" => 		new Field("num",	"Candidate Name")  );



/*  --------------------------------------------- ELECTIONS ----- */
$name = "election";
$megastructure[$name."s"] = array(
	$name."_id" => 			new Field("key",	"Election ID"),
	$name."_name" => 		new Field("string",	"Election Name"),
	$name."_startdate" => 		new Field("string",	"Election Start Date"),
	$name."_enddate" => 		new Field("string",	"Election End Date")  );



/*  --------------------------------------------- RACES ----- */
$name = "race";
$megastructure[$name."s"] = array(
	"election_id" => 		new Field("num",	"Election ID"),
	$name."_id" => 			new Field("key",	"Race ID"),
	$name."_name" => 		new Field("text",	"Race Name")  );
$megastructure[$name."s"]["election_id"]->set("keyOfTable","elections");



/*  --------------------------------------------- RECEIPTAUDITS ----- */
$name = "receiptaudit";
$megastructure[$name."s"] = array(
	"left_receipt_id" => 		new Field("key",	"Left Receipt ID"),
	"right_receipt_id" => 		new Field("num",	"Right Receipt ID"),
	"audit_germ" => 		new Field("num",	"Audit Germ")  );



/*  --------------------------------------------- RECEIPTS ----- */
$name = "receipt";
$megastructure[$name."s"] = array(
	$name."_id" => 			new Field("key",	"Receipt ID"),
	"election_id" => 		new Field("num",	"Election ID"),
	"race_id" => 			new Field("num",	"Race ID"),
	"teller_id" => 			new Field("num",	"Teller ID"),
	"teller_batch" => 		new Field("num",	"Teller Batch"),
	"receipt_partialform" => 	new Field("blob",	"Receipt Partial Form"),
	"partialform_plaintext_vote" => new Field("string",	"Receipt Plaintext Vote")  );
$megastructure[$name."s"]["election_id"]->set("keyOfTable","elections");
$megastructure[$name."s"]["race_id"]->set("keyOfTable","races");
$megastructure[$name."s"]["teller_id"]->set("keyOfTable","tellers");



/*  --------------------------------------------- TELLERS ----- */
$name = "teller";
$megastructure[$name."s"] = array(
	$name."_id" => 			new Field("key",	"Teller ID"),
	$name."_name" => 		new Field("string",	"Teller Name"),
	$name."_ipaddress" => 		new Field("string",	"Teller IP Address"),
	$name."_servername" =>		new Field("string",	"Teller Server Name"),
	$name."_publickey" => 		new Field("blob",	"Teller Public Key"),
	$name."_sequencenumber" => 	new Field("num",	"Teller Sequence Number")   );


$name = "tally";
$megastructure["tallies"] = array(
	"election_id" => 		new Field("num",	"Election ID"),
	"race_id" => 			new Field("num",	"Race ID"),
	$name."_round" => 		new Field("string",	"Tallying Round"),
	"candidate_id" => 		new Field("blob",	"Candidate ID"),
	$name."_votes" => 		new Field("num",	"Number of votes")   );


?>