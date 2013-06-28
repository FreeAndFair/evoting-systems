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
$db_username = "php";				// database username
$db_password = "onions";			// database password
$db_databasename = "pretavoter3";		// name of db on server
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


/** ****************************************** Remote Voter
  * Parameters for the Remote Voter stuff *
  */
$rvtable = "remotevote";



?>