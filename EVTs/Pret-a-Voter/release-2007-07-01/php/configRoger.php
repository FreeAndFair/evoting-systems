<?php

/** config.php holds all the parameters, that are necessary
  * for the whole system to work. Put all customisation variables
  * here, to keep things together.
  */
include_once("fieldclass4.php");
include_once("db4.php");
include_once("megastructure.php");
include_once("recclass4.php");
include_once("functioncollection.php");


/** ******************************************* Database
  * Parameters for the database *
  */
$db_host = "localhost";				// database host server name
$db_username = "root";				// database username
$db_password = "rootroot";			// database password
$db_databasename = "pav2";		// name of db on server
$db_port = false;				// optional, port to connect to

// Table names
$auditmachinetable = "auditmachines";
$ballotformstable = "ballotforms";
$booths = "booths";
$candidateraces = "candidateraces";
$candidates = "candidates";
$elections = "elections";
$races = "races";
$tellers = "tellers";

$db = new db($db_host , $db_username , $db_password , $db_databasename,  $db_port);
// **********************************************************************************



/** ******************************************* DB lookups
  * DB lookup parameters
  */
$furtherinfopage = "furtherinfo.php";

// **********************************************************************************



/** ****************************************** Races
  * Election races information
  */
$racesArr = array(5,6,2);
$race_types = array('stv','stv','x');
$race_titles = array('Who should be spared from being thrown out of the hot air balloon','What is your favourite programming language','Have you ever lied on an expenses form?');
$races_candidates= array();

/** TODO: Set up the following values to be the names of the candidates in canonical order */
$races_candidates[0] = array("Alistair McEwan","Chris Culnane","Chuck them all out!","Michelle Greensit","Nick Anderson");
$races_candidates[1] = array("C++","Hand-coded Z80 assembler","I make my PhD student do all my programming","Java","Perl","Python");
$races_candidates[2] = array("No","Yes");
// **********************************************************************************



/** ****************************************** Remote Voter
  * Parameters for the Remote Voter stuff *
  */
$rvtable = "remotevote";



?>