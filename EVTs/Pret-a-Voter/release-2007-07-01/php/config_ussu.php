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
$db_databasename = "pretavoter";		// name of db on server
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
$racesArr = array(3,2,3,2,2,2,2);
$race_types = array('stv','stv','stv','stv','stv','x','x');
$race_titles = array("Union President","VP Sports and Recreation","VP Societies and Individual Development","VP Education","VP Welfare","Should the Student Union continue its membership with the National Union of Students (NUS)?","Do you agree with the university's fairtrade policy and support the University's efforts towards attaining Fairtrade University status?");
// **********************************************************************************

/** ****************************************** Remote Voter
  * Parameters for the Remote Voter stuff *
  */
$rvtable = "remotevote";



?>