<?php

  /** This script processes the request for a submitted vote status page
    * . Initiate session
    * . Log URN, URL, IP, timedatestamp
    * . check session variables, retrieve database table
    * . return to user 
    */

//include_once("../db.php");
include_once("rv.php");
include_once("config.php");

// Initiate Session
session_start();

// Get their database details
$session_urn = $_SESSION['store_urn'];
$session_password = $_SESSION['store_password'];

// Get their IP 
$ip = $_SERVER['REMOTE_ADDR'];
$_SESSION['IP'] = $ip;
logstuff("complete.php: page access by $ip, as urn:$session_urn");


$sql = "SELECT * FROM remotevote WHERE urn=$session_urn LIMIT 1";
$resArr = $db->queryArr($sql);
if(is_array($resArr) && (count($resArr) > 0)) {
  $db_password = $resArr[0]['password'];
  if($db_password != $session_password) {
    ?><meta http-equiv="refresh" content="0; url=loginpage.php<?
    if($session_urn) echo("?urn=".$session_urn); ?>" /><?
    exit();
  } else {
    $db_ballot_serial = $resArr[0]['ballot_serial'];
    $db_reached_stage = $resArr[0]['reached_stage'];
    $db_vote = $resArr[0]['vote'];
    $db_receipt_string = $resArr[0]['receipt_string'];
  }
} else die("Could not access database.<meta http-equiv='refresh' content='20; url=complete.php' />");

// Head of page
$titleprefix = "Submitted vote status";
include("header.php");

?>
<div id="mainlinks">
  Log in<br />
</div>

<div id="mainvider">
   <!-- nowt -->&nbsp;
</div>
<div id="maincontent">

<div id="maintitle">Vote status: <? echo("$db_reached_stage"); ?></div>
<h3>VOTE RECEIPT</h3>
<? //---------------------------------------------------------------------------------------
echo("<!-- $db_receipt_string -->");

echo receiptHTML($db_receipt_string);











// -----------------------------------------------------------------------------------------
?>
</div>
<? include("footer.php"); ?>