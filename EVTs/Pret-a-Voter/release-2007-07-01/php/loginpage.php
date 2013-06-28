<?php

  /** This script processes the request for a login page
    * . Initiate session
    * . Log URN, URL, IP, timedatestamp
    * . serve up login page with URN embedded, box for password 
    */

//include_once("db4.php");
include_once("rv.php");
include_once("config.php");

// Initiate Session
session_start();

// Set stage to login, note session id
$_SESSION['stage'] = "login";
$_SESSION['id'] = session_id();
//echo $_SESSION['id']."<br />\n";

// Get their IP 
$ip = $_SERVER['REMOTE_ADDR'];
$_SESSION['IP'] = $ip;
logstuff("loginpage: Login page access by $ip");

/*
remotevotes:
. id
. urn
. ballot_serial
. password
. reached_stage
. vote
. receipt_string
*/

/* CREATE TABLE `remotevote` (
`id` INT( 10 ) NOT NULL AUTO_INCREMENT PRIMARY KEY ,
`urn` TEXT NOT NULL ,
`ballot_serial` TEXT NOT NULL ,
`password` TEXT NOT NULL ,
`reached_stage` VARCHAR( 5 ) NOT NULL ,
`vote` TEXT NOT NULL ,
`receipt_string` LONGTEXT NOT NULL
) ENGINE = MYISAM ;
*/

// Head of page
$titleprefix = "Log in";
include("header.php");

?>
<div id="mainlinks">
  Log in<br />
</div>

<div id="mainvider">
   <!-- nowt -->&nbsp;
</div>
<div id="maincontent">

<div id="maintitle">Log in</div>

<form method="GET" action="castvote.php">
<input type=hidden name="sessionchk" value="<? echo($_SESSION['id']); ?>">
<?

// Check the URN is in the query string
if(isset($_GET['urn'])) {
  $urn = $_GET['urn'];
  ?><h3>URN:</h3><? echo($urn) ?></h3>
<input type=hidden name="urn" value="<? echo($urn) ?>">
<p>Your URN is shown above.</p>
<?

} else {
  ?><h3>Missing URN</h3>
<p>No URN provided. Only those previously registered to vote remotely may do so. If you did register, click the link in your email, or enter your URN here:

<input type="text" name="urn" /><br />
<?
}

?>
<h3>Password</h3>
<p>In the email you received, you were given a password. Please enter it here (copy and paste is easiest).</p>

<input type="text" name="password"><br />
<br />
<input type=submit value="Log in">
<?
//echo("rv:".$rv);
//echo(getstring());

?>

</form>

</div>
<? include("footer.php"); ?>