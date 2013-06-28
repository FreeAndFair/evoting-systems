<?php

/** Progress.php receives the submitted vote form, and handles it. If the form has
  * been submitted incorrectly, the user is returned to the castvote page. If the
  * form is ok, the user is asked to wait, and kept up to date on the progress of
  * the submission. Simple refresh mechanism, keep life simple.
  */

/** TODO: Fix brackets problem? 
  * TODO: Check reporting correctly.
  * TODO: What are those unspaced commas doing?
  */
//include_once("../db.php");
require_once("rv.php");
include_once("config.php");

// Initiate Session
session_start();

// Insert head of page (title etc)
$titleprefix = "Vote Progress";
include("header.php");
?>    <div id="mainlinks">
Log in<br />
Vote progress<br />
    </div>
    <div id="mainvider">
      <!-- nowt -->&nbsp;
    </div>
    <div id="maincontent">
      <div id="maintitle">Vote Progress</div>

<?
// Get session variables
$session_id = $_SESSION['id'];
$session_stage = $_SESSION['stage'];
$session_ip = $_SESSION['IP'];
if(isset($_SESSION['raceErrs'])) unset($_SESSION['raceErrs']);
$_SESSION['raceErrs'] = array();
if(isset($_SESSION['raceWarns'])) unset($_SESSION['raceWarns']);
$_SESSION['raceWarns'] = array();

// Get login post variables
if(ctype_alnum($_POST['sessionchk'])) $post_id = $_POST['sessionchk'];
if(ctype_digit($_POST['urn'])) $post_urn = $_POST['urn'];
if(ctype_alnum($_POST['password'])) $post_password = $_POST['password'];

// Get their IP 
$ip = $_SERVER['REMOTE_ADDR'];
$_SESSION['IP'] = $ip;
logstuff("progress.php: progress page access by $ip, as urn:$post_urn");

// Check to see if the user is logged in. 
if(isset($_SESSION['stage']) && ($stages[$session_stage]>=$stages["vote"]) && ($session_id == $post_id)) {
  $flagLoggedIn = true;
} else {
  ?>  <h3>Not logged in</h3>
  <p>You are being returned to the login page. Check your urn and password.</p>
  <? /** echo("stage set? ".isset($_SESSION['stage'])."<br />\n");
     echo("stage # of session stage:".$stages[$session_stage]."<br />\n");
     echo("stage # of vote:".$stages["vote"]."<br />\n");
     echo("session id:".$session_id."<br />\n");
     echo("post id:".$post_id."<br />\n"); */
  ?>
  <meta http-equiv="refresh" content="30; url=loginpage.php?urn=<? echo($post_urn); ?>" />
<?
  exit();
} 

// Check to see if they've already voted
if(isset($_SESSION['stage']) && ($stages[$session_stage]>$stages["vote"]) && ($session_id == $post_id)) {
  //look them up in the database
  $stage = getvotingstage($_SESSION['store_urn'],$_SESSION['store_password']);
  if($stages[$stage] > $stage["vote"]) {

    // Already voted!
    ?>  <h3>Vote stage: <? echo($stages[$stage]) ?></h3>
    <p>You are being forwarded to the submitted vote status page for more details of your vote.</p>
    <? /** echo("stage set? ".isset($_SESSION['stage'])."<br />\n");
       echo("stage # of session stage:".$stages[$session_stage]."<br />\n");
       echo("stage # of vote:".$stages["vote"]."<br />\n");
       echo("session id:".$session_id."<br />\n");
       echo("post id:".$post_id."<br />\n"); */
    ?>
    <meta http-equiv="refresh" content="30; url=complete.php" /> 
    <?
    exit();
  }
} 


// So we have a logged in user. Check their vote form.
/** TODO: code to generate the array goes here */
/*$races = array(3,4,3,2,2,2,2);
$race_types = array('stv','stv','stv','stv','stv','x','x');
$race_titles = array("Union President","VP Sports and Recreation","VP Societies and Individual Development","VP Education","VP Welfare","Should the Student Union continue its membership with the National Union of Students (NUS)?","Do you agree with the university's fairtrade policy and support the University's efforts towards attaining Fairtrade University status?");*/
global $races;
global $race_types;
global $race_titles;

$errMsg = "";
$all = array();
/** TODO: Delete the debug stuff, ie this next row */
?><!--<?

foreach($races as $race => $candidates) {

echo("Race: $race ($candidates candidates)<br />\n");

  // Retrieve the data on this race
  $flagDataOK = true;

  // Unset data var
  if(isset($data)) unset($data);

  /* --------------------------------------- STV --------------------- */
  if($race_types[$race] == "stv") {
echo("Race type: {$race_types[$race]}<br />\n");

    // data is for the sequential list of numbers, ie 1,3,4,2
    $data = array();

    // counter is to count how many times a ranking comes up.
    $counter = array();

    // go through, incrementing the count for each rank that it finds
    for($i=1;$i<=$candidates;$i++) {
echo("Candidate: $i <br />\n");

      // name of form element
      $name = "race".$race."_".$i;
echo("Post data($name): {$_POST[$name]} <br />\n");

      // codify choice
      if(ctype_digit($_POST[$name])) { //rank
        $data[$i] = $_POST[$name];
        $counter[$data[$i]] += 1;
      } elseif (($_POST[$name] == "-")) { //unranked
        $data[$i] = "-";
      }
echo(".Data: {$data[$i]} <br />\n");

    }

    /** Check for malformed vote in this race */
    // Check whether any vote was cast in this race
    if(is_array($counter) && count($counter)>0) {

      // Check for duplicate rankings - two 1s, etc
      if(max($counter) != 1) {

        // Register error for later
        $flagDataOK = false;
        $_SESSION["raceErrs"][$race] .= "<p class='error'>Entry contained more than one candidate with the same ranking. Only one candidate can have each rank number.</p>";

      } else {
        /** Have no duplicate rankings, but are they in a sensible order?
          * Check this by looking for any rankings that are not in the right range - 
          * if there are ranks 1-3, and there are no duplicates, then 1-3 are the
          * only legitimate numbers. */
        $num_ranks = array_sum($counter);
        $largest_rank_num = max($data);

        if($num_ranks != $largest_rank_num) {
          // Not a sequential list from 1. Append error to errormsg and flag it.
          $flagDataOK = false;
          $_SESSION["raceErrs"][$race] .= "<p class='error'>Entry wasn't sequential. List only choice 1,2,3 etc. Do not leave gaps (1,3,4) in the list.</p>";
        }
      }

    } else {
      // voter has selected nothing in this race
      $emptyraces[] = $race;
      // set race error for castvote page, if we're going back there.
      $_SESSION["raceWarns"][$race] = "<p class='warning'>No vote cast in this race. Are you sure you don't want to vote?</p>";
    }

    //keep the value somewhere.
    if($flagDataOK) {
      $all[$race] = "";
      for($i=1;$i<=$candidates;$i++) {
        $all[$race] .= $data[$i];
      }
      echo("ALL: $all[$race]: ".$all[$race]." <br />\n");
      $data_all[$race] = $data;
    }
  /* --------------------------------------- X --------------------- */
  } else {  // X type

    /* Check that the value is a possible one. */
    // get the value
    if(ctype_alnum($_POST['race'.$race])) {
      $data = $_POST["race$race"];
      echo("--race:$race, data:$data<br />\n");
      
      // test value is in range
      if(($data < 1 ) || ($data > $candidates)) {
        $flagDataOK = false;
        $_SESSION["raceErrs"][$race] .= "<p class='error'>Vote was not valid. Ensure that you have chosen out of the available options.</p>";
      }

    } else {
      // Vote not cast
      $data = '';
      $emptyraces[] = $race;
      $_SESSION["raceWarns"][$race] .= "<p class='warning'>No vote cast. Are you sure you don't want to vote?</p>";
    }

    // Store data
    $data_all[$race] = $data;
    for($i=1;$i<=$candidates;$i++) {
echo("Candidate: $i, vote:$data <br />\n");
      if($i == $data) {
        $all[$race] .= "x";
      } else {
        $all[$race] .= "o";
      }
    }

  }
}

/** TODO: Delete the debug stuff, ie this next row */
?>--><?

// Setup review url for going back and fixing things
$reviewurl = "castvote.php".poststring();

// Empty races?
$ballot_is_empty = false;
if(is_array($emptyraces) && (count($emptyraces)>=count($races))) {
  // No votes cast for anything. Not allowed.
  ?><h3>No votes cast</h3><p>No votes were cast. You cannot cast an empty vote. You must choose to vote in at least one race.</p><? 
  $ballot_is_empty = true;
}

/* Provide errors and warnings */
// Errors
$noerrs = (count($_SESSION["raceErrs"]) <= 0);
if(!$noerrs) {
  ?><h3>Errors</h3><p>There were errors in the vote cast. These are listed below, and must be <a href="<? echo($reviewurl) ?>">corrected</a> before the vote can be submitted:</p>
<?

  $errs = $_SESSION["raceErrs"];
  foreach($errs as $race=>$err) {
    ?><h4 style="color:red"><? echo($race_titles[$race]) ?></h4>
<?  echo($err);
  }
}


// Warnings
$nowarns = (count($_SESSION["raceWarns"]) <= 0);
echo("count warns: ".count($_SESSION["raceWarns"]));
if(!$nowarns && !$_POST['warnsok']) {
  echo("<h3>Warnings</h3><p>Some warnings about the vote cast are listed below. If you wish to change your vote, click <a href='$reviewurl'>review</a>:</p>\n");

  $warns = $_SESSION["raceWarns"];
  foreach($warns as $race=>$warn) {
    ?><h4><? echo($race_titles[$race]) ?></h4>
<?  echo($warn);
  }
}

// Print out all the data
$all_string = implode(",",$all);
echo("Votecast string: '".$all_string."'<br />\n");


// Save votes cast to session variable
$_SESSION['votes_string'] = $all_string;
$_SESSION['previousdata'] = $all;
$_SESSION['flagReview'] = true;

// Warns OKed?
$warnsok = isset($_POST['warnsok']) && ($_POST['warnsok']=="true");
if(!$warnsok && $noerrs && (!$nowarns)) {
  ?><form method="POST" action="progress.php"><?
  foreach($_POST as $key=>$value) {
    echo("<input type=hidden name='$key' value='$value' />\n");
  }
  ?><input type=hidden name='warnsok' value='true' />
  <h4>Proceed ignoring warnings?</h4>
  <input type=submit value='Proceed anyway' />
  </form><?

}

// Flush so far
ob_flush();flush();

// Cast vote or not? 
$cast = ($nowarns || $warnsok) && $noerrs && (!$ballot_is_empty); 
echo("nowarns: $nowarns, warnsok: $warnsok, noerrs: $noerrs, ballot_is_empty: $ballot_is_empty<br />");
if($cast) {
echo("CAST");
exit;
  /** Get hold of the serial and signed hash hex string 
    * TODO: Pull serial and signed hash out of database 
    */
  // For now, pretend
  //$serial = "98765";
  //$signed_hash = "a1b2c3d4e5";
  $arr = $db->queryArr("SELECT * FROM remotevote WHERE urn=$post_urn LIMIT 1");
  $vals = $arr[0];
  $serial = $vals["ballot_serial"];
  $signed_hash = $vals["ballot_signedhashhex"];


  // Put the serial number on the front
  $submit_string = "10,".$serial.",".$signed_hash.",".$all_string;

  // Uprate user stage to processing, trust that it manages the next few lines
  upstage($post_urn, $post_password,"processing");

  // Open parallel process to follow the commandline. Code straight from php.net (Cride5 of solidsites.co.uk)
  //$handle = popen("tail -f /etc/httpd/logs/access.log 2>&1", 'r');
  //$handle = popen('java whateverClass "'.$submit_string.'" 2>&1', 'r');
  $flagReturning;
  ?><p>Initiating vote submission, please be patient while the vote is processed by the system and your receipt is generated.</p><?
  ob_flush();flush();

// ----------
  //simulate a slowish process 
  $exec_string = "curl http://131.227.68.245/index.php?csv=$submit_string";
  $handle = popen($exec_string,'r'); 
  if(!$handle) {
    // Assume nothing worked, downgrade user
    downstage($post_urn,$post_password,"vote");
    ?>Vote submission attempt failed. Please retry later.<?
  } else {
    sleep(1);
    while(!feof($handle)) {
      $buffer = fgets($handle);
      $all_buffer .= $buffer;
      if($flagReturning == false) {
        upstage($post_urn,$post_password,"returning");
        $flagReturning = true;
        ?>      <p>Your vote has been submitted. You cannot submit any further votes, or make any changes to the vote you have already submitted. Logging in again in the future will only provide you with access to this information.</p>
Returning receipt, please retain a copy, this proves your vote has been submitted:<br />
        <h3>VOTE RECEIPT</h3><?
      }
      //echo "$buffer<!-- buf -->";
      //ob_flush();
      //flush();
    }
    pclose($handle);
  }

//-------------
  echo("<!-- whole buffer:\n$all_buffer\n -->");

  upstage($post_urn,$post_password,"complete");

  // get the votes
  $receiptvotes = array_slice(explode(",",$all_buffer),5);


  /**  ***** Fill the boxesdata array **************** */
  $boxesdata = array();

  global $races;
  foreach($races as $race=>$candidates) {
   
    /* example:
     * $boxesdata[0] = array( 	1=>"a1",
				2=>"a2",
				3=>"a3");  */

    $boxesdata[$race] = array();
 
    for($i=1;$i<=$candidates;$i++) {
      $thisval = $receiptvotes[$race][$i];

      /** TODO: Do any kind of processing, like converting to image version 
        *    -> translateVoteMarks func (in collection) */
      $htmlcontents = translateVoteMarks($thisval);

      $boxesdata[$race][$i] = $htmlcontents;
    }

  }

  // spit out all the HTML for this ballot form
  echo ballotHTML($boxesdata);

  global $db;
  $db->query("UPDATE remotevote SET vote='$all_string' LIMIT 1");

  enterReceipt($post_urn,$post_password,implode(",",$receiptvotes));

  exec("echo 'urn $post_urn, buf $all_buffer' | mail php2ph ");

?>

      </div>


<? 
}


include("footer.php");
?>