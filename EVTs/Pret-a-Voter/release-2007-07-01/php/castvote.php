<?php

  /** This script processes the request for a login page
    * . Initiate session
    * . Log URN, URL, IP, timedatestamp
    * . serve up login page with URN embedded, box for password 
    */

  /** TODO: Write section retrieving previous data from session */

include_once("rv.php");
include_once("config.php");

// Initiate Session
session_start();


// Insert head of page (title etc). getstring() in rv.php
$titleprefix = "Cast Vote";
include("header.php");
?><div id="mainlinks">
<a href="loginpage.php">Log in</a><br />
<a href="castvote.php?urn=<? echo(getstring()); ?>">Cast vote</a><br />
    </div>
    <div id="mainvider">
      <!-- nowt -->&nbsp;
    </div>
    <div id="maincontent">
      <div id="maintitle">Cast Vote</div>
<?
// Retrieve variables from the session, check against page
$session_id = $_SESSION['id'];
$session_stage = $_SESSION['stage'];
$session_ip = $_SESSION['IP'];
if(isset($_SESSION['flagReview']) && ($_SESSION['flagReview'] == true)) {
  $flag_review = true;
  $prevs = $_SESSION['previousdata'];
} else {
  $flag_review = false;
}

// Retrieve variables from the GET
if(ctype_alnum($_GET['sessionchk'])) $get_id = $_GET['sessionchk'];
if(ctype_digit($_GET['urn'])) $get_urn = $_GET['urn'];
if(ctype_alnum($_GET['password'])) $get_password = $_GET['password'];


// Get their IP, log
$ip = $_SERVER['REMOTE_ADDR'];
$_SESSION['IP'] = $ip;
logstuff("castvote: Cast Vote page access by $ip, as urn:$get_urn");



/*echo("Session id:".$session_id."<br />\n");
echo("Session stage:".$session_stage."<br />\n");
echo("Session ip:".$session_ip."<br />\n");
echo("Get id:".$get_id."<br />\n");
echo("Get urn:".$get_urn."<br />\n");
echo("Get_password:".$get_password."<br />\n");*/

// Check the urn exists
$sql = "SELECT COUNT(*) FROM $rvtable WHERE urn=$get_urn";
$res = $db->queryArr($sql);
$count = intval($res[0]['COUNT(*)']);

// If the URN exists, go ahead and retrieve some things from the database.
//  Otherwise, don't bother.
if($count == 0) {
  $flagNOURN = true;
} else {

// Get their data from the table
$sql = "SELECT * FROM $rvtable WHERE urn=$get_urn LIMIT 1";
$res = $db->queryArr($sql);
$data = $res[0];
$db_id = $data['id'];
$db_urn = $data['urn'];
$db_ballot_serial = $data['ballot_serial'];
$db_password = $data['password'];
$db_reached_stage = $data['reached_stage'];
$db_vote = $data['vote'];
$db_receipt_string = $data['receipt_string'];
$_SESSION['store_urn'] = $get_urn;
$_SESSION['store_password'] = $get_password;

/* echo("Some db stuff: id: $db_id, urn: $db_urn, ballot serial:$db_ballot_serial, password: $db_password, reached_stage: $db_reached_stage, vote: $db_vote, receipt string: $db_receipt_string <br />\n");*/

}

// Check their login. If not ok, give them a meta refresh and quit.
if((($res) && ($db_urn == $get_urn) && ($get_password != $db_password)) || $flagNOURN) {
?>
  <h3>Incorrect login</h3>
  <p>You are being returned to the login page. Check your urn and password.</p>
  <meta http-equiv="refresh" content="3; url=loginpage.php<?
  if($get_urn) echo("?urn=".$get_urn); ?>" />
<?php
  logstuff("castvote.php: incorrect login. urn:$get_urn");
  exit();
}

/**  Check their stage in the database. If it's processing, returning or complete
  *   then redirect them.
  *  Otherwise, give them the voting page.*/
// Check if the vote has already been submitted
if($stages[$db_reached_stage]>$stages["vote"]) {

    // Already voted!
    ?>  <h3>Vote stage: <? echo($stages[$stage]) ?></h3>
    <p>You are being forwarded to the submitted vote status page for more details of your vote.</p>
    <? /** echo("stage set? ".isset($_SESSION['stage'])."<br />\n");
       echo("stage # of session stage:".$stages[$session_stage]."<br />\n");
       echo("stage # of vote:".$stages["vote"]."<br />\n");
       echo("session id:".$session_id."<br />\n");
       echo("post id:".$post_id."<br />\n"); */

       logstuff("castvote.php: voter (urn:$get_urn) already at stage $session_stage according to session data.");
    ?>
    <meta http-equiv="refresh" content="5; url=complete.php" /> 
    <?
    exit();
  }

// So now we have an authenticated user, who has not cast a vote. Give them the form!
$db_reached_stage = "vote";
$up_res = upstage($get_urn, $get_password, "vote");
logstuff("castvote.php: Uprated user to 'vote' stage. result:$up_res");
$_SESSION['stage'] = $db_reached_stage;
?>
<form method="POST" action="progress.php">
<input type=hidden name=urn value="<? echo($get_urn) ?>" />
<input type=hidden name=sessionchk value="<? echo($get_id) ?>" />
<input type=hidden name=password value="<? echo($get_password) ?>" />
<?

// Need to get details of the races. 
/** TODO: code to generate the array goes here */
$races = array(3,2,3,2,2,2,2);
$race_types = array('stv','stv','stv','stv','stv','x','x');
$race_titles = array("Union President","VP Sports and Recreation","VP Societies and Individual Development","VP Education","VP Welfare","Should the Student Union continue its membership with the National Union of Students (NUS)?","Do you agree with the university's fairtrade policy and support the University's efforts towards attaining Fairtrade University status?");


// Setup default values, if there are no previous values to use
if(!$flag_review) {
  $prevs = array();
  foreach ($races as $race=>$candidates) {
    for($k=1;$k<=$candidates;$k++) {
      if($race_types[$race]=="stv")
        $prevs[$race] .= '-';
      else
        $prevs[$race] .= 'o';
    }
  }
}

/* echo("----<br />PREVS:<br />");
foreach($prevs as $key=>$val) {
  echo($val."<br />");
} */


// Determine total height. Gap between each race:
$h_gap = 1.2;
$total = 0;
foreach($races as $race => $candidates) {
  $total += $candidates + $h_gap;
}
$height_unit = 100/$total;


// Seed the random number generator (for the bg colors)
srand(7538);


// Generate the div structure
?><div id="ballot"><?
$colour = 0;

foreach($races as $race => $candidates) {
  $type = $race_types[$race];

  //retrieve previous data for this race;
  //if($flag_review) 
    $prev = $prevs[$race];

  // write out the candidate box, each race with a different background shade
  $colour = dechex(rand(225,253))."".dechex(rand(225,253))."".dechex(rand(225,255));
  ?><div class="race" style="background-color:#<? echo($colour) ?>; height:<? echo($height_unit * $candidates) ?>%; padding-top:<? echo($height_unit*$h_gap) ?>%;">
  <div class="racename" style="height:100%">
    <? echo($race_titles[$race]) ?></div>
    <div class="candidatebox" style="height:100%"><?


    // HTML for a candidate choice
    for($i=1;$i<=$candidates;$i++) {
      $elem_name = "race{$race}_{$i}";
      ?><div class='candidate' style="height:<? echo(100/$candidates) ?>%">
<?
      /*     Provide dropdowns for STV race     */
      if($race_types[$race] == "stv") {
        echo("<select name='".$elem_name."'><option value='-' ");
        if($prevs[$race][$i-1] == "-") echo('selected="selected"');
        echo(">-</option>");
        for($j=1;$j<=$candidates;$j++) {
          echo("<option value='$j' ");
          if($prevs[$race][$i-1]==$j) echo('selected="selected" ');
          echo(">$j</option>\n");
        }
?>      </select><?

        /* Add clear button after the last candidate  */
        // Collect text for javascript
        $js .= "document.forms[0].$elem_name.selectedIndex=0;\n";

        if($i == $candidates) { 
          // Last candidate, so add clear button.
          ?><input type=button style="margin-left:1em" value="Clear" onClick="<? echo($js) ?>" />
<?      }
      } else {
        /*     Provide radio buttons for X type race   */
        $elem_name = "race$race";
        echo("<input type=radio value='$i' name='$elem_name' ");
        if($prevs[$race][$i-1] == "x") echo("checked ");
        echo(" />");

        // Add clear button after last candidate
        if($i == $candidates) {
          // Last candidate
          ?><input type="button" style="margin-left:1em" value="Clear" onClick="<?
          for($k=0;$k<$candidates;$k++) {
            echo("document.forms[0].{$elem_name}[$k].checked=false;\n");
          }
          ?>" />
<?      }
      }
      ?></div><?
    }

    ?></div>
  </div>
<?
}
?></div><?

/* Add submit and reset buttons */
?><input type=submit value="Cast Vote" />
<input type=reset value="Reset" />
</form>
</div>
<? include("footer.php"); ?>