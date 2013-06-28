<?php 

/** rv.php holds central stuff like the stage process:
 * login: set by the login page. Waiting for the user to 
 *	log in and proceed to castvote.php.
 * vote: set by the castvote page. Waiting for the user to
 *	correctly cast their vote, ie submit to processvote.php
 * processing: set by the processvote page. This is the status
 *	until the java program has finished running
 * returning: this stage for the time after receiving the reply
 *	from the java program, and sending it to the user.
 * complete: the receipt has been returned to the user.
 * ---
 * Once the user reaches processing, they cannot drop back to 'vote'.
 * If they go to the login page and log in successfuly, they will
 * simply be presented with their receipt.
 */

$stages = array(	'' 		=> 0,
			'login'		=> 1,
			'vote'		=> 2,
			'processing'	=> 3,
			'returning'	=> 4,
			'complete'	=> 5,
			'error'		=> 6);

$stage_explanations = array( 0=>"Not logged in yet",
			1=>"Login stage",
			2=>"Logged in correctly, now ready to cast a vote",
			3=>"Vote has been cast correctly, and is being submitted to the main voting system",
			4=>"The system has registered the vote and is returning its reply",
			5=>"Voting process complete. Receipt available.",
			6=>"Error in the voting process. Please alert the administrator (p.howard [at] surrey [dot] ac [dot] uk)");
$rv = 6;

// Getstring returns all the _GET queries as a string
function getstring() {
  $ret = "?";
  $getarr = array();
  foreach($_GET as $key => $value) {
    $getarr[] = "$key=$value";
  }
  $ret .= implode("&",$getarr);
  return $ret;
}

// Poststring returns all the _POST queries as a string
function poststring() {
  $ret = "?";
  $postarr = array();
  foreach($_POST as $key => $value) {
    $postarr[] = "$key=$value";
  }
  $ret .= implode("&",$postarr);
  return $ret;
}

// Votingdone checks to see what stage this remotevoter has so far 
//   completed, unless the password is wrong, when it returns -1.
function getvotingstage($urn,$password) {
  $sql = "SELECT password,reached_stage FROM remotevote WHERE urn=$urn LIMIT 1";

  global $db;
  $db_arr = $db->queryArr($sql);
  $db_pass = $db_arr[0]['password'];
  $db_stage = $db_arr[0]['reached_stage'];

  if($db_stage == "error") logstuff("Stage 6 (ERROR) reached by remote voter urn:$urn.");

  if($password == $db_pass) {
    return $db_stage;
  } else {
    return -1;
  }


}

// Log things to a file.
function logstuff($stringtolog) {
 
  // Open file to append log
  //$fp = fopen("remotevoter.log", "a");

  $time = time();
  $ltimeArr = localtime(time(),true);
  $hour = $ltimeArr['tm_hour'];
  $min = $ltimeArr['tm_min'];
  $sec = $ltimeArr['tm_sec'];

  $str = "\n".time()." , ".date('Y-m-d')." $hour:$min:$sec , ".$stringtolog;
  // Write data, close
  //fwrite($fp, $str);
  //fclose($fp);

  return true;
}


// Uprate user to a particular stage.
//   Returns false if they are already at or above this.
function upstage($urn,$password,$tostage) {

  global $stages;
  // check current stage first
  $current_stage = getvotingstage($urn,$password);
  
  if(!isset($stages[$tostage])) {
    logstuff("upstage: cannot uprate user(urn:$urn)'s stage to $tostage. Stage name not valid, see rv program file.\n");
    return false;
  } elseif($stages[$current_stage] >= $stages[$tostage]) {
    logstuff("upstage: cannot uprate user(urn:$urn)'s stage to $tostage ({$stages[$tostage]}). Already at $current_stage ({$stages[$current_stage]}).");
    return false;
  } else {
    $sql = "UPDATE remotevote SET reached_stage='$tostage' WHERE urn=$urn LIMIT 1";
    global $db;
    $db->query($sql);
    return true;
  }

}

// Downrate user to a particular stage.
//   Returns false if they are already below this stage.
function downstage($urn,$password,$tostage) {

  global $stages;

  // check current stage first
  $current_stage = getvotingstage($urn,$password);
  
  if(!isset($stages[$tostage])) {
    logstuff("downstage: cannot uprate user(urn:$urn)'s stage to $tostage. Stage name not valid, see rv program file.\n");
    return false;
  } elseif($stages[$current_stage] <= $stages[$tostage]) {
    logstuff("upstage: cannot downrate user(urn:$urn)'s stage to $tostage ({$stages[$tostage]}). Already at $current_stage ({$stages[$current_stage]}).");
    return false;
  } else {
    $sql = "UPDATE remotevote SET reached_stage='$tostage' WHERE urn=$urn LIMIT 1";
    global $db;
    $db->query($sql);
    return true;
  }

}

// enterReceipt updates the remotevote table with the receipt
//   Returns false if cannot insert into database
function enterReceipt($urn,$password,$receiptstring) {

  // check current stage first, use for password checking
  $current_stage = getvotingstage($urn,$password);

  // now put the receipt in
  if($current_stage == -1) {
    logstuff("enterReceipt: cannot enter receipt string for user(urn:$urn). Incorrect password($password). Receipt supplied:[".$receiptstring."]\n");
    return false;
  } else {
    $sql = "UPDATE remotevote SET receipt_string='$receiptstring' WHERE urn=$urn LIMIT 1";
    logstuff("enterReceipt: trying to enter [$sql]");
    global $db;
    $res = $db->query($sql);
    logstuff("enterReceipt: result: $res");
    return true;
  }

}
?>