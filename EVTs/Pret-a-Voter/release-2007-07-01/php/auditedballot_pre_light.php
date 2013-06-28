<?php

/** auditedballot.php
  * This page looks up a ballot form that has been audited (rather than voted with),
  * and displays the information to the user. 
  * Method:
  * . Make sure we've got an audited ballot number.
  * . If not, ask for a number, say if that ballot has not been audited
  * . Retrieve ballot information
  * . For each race
  * .. generate a table showing the permutations producing a result

  * Much of this adapted from receiptlookup.php
  **/

  // includes
  include_once("config.php");

  // Get the debug switch
  if(isset($_GET['debug'])) {
    $debug = $_GET['debug'];
  } else {
    $debug = 0;
  }

  // These TDs arrays will hold the actual names of the candidates. 
  var $initialTDs;
  var $finalTDs; 

  // do head of html page
  $titleprefix = "Audited Ballot Lookup";
  if($debug) $titleprefix .= " - debug";
  include("header.php");


  $flagEnterSerial = false;

  // check if serial number has been given. if not, flagEnterSerial
  if(isset($_GET['serial'])) {
    $serial = no_nasties($_GET['serial']);

    if($debug) echo("have serial<br />");
    if(ctype_digit($serial) && $serial) {

      // serial number has been given. check has been audited, if not, flagEnterSerial.
      if($debug) echo("it has numbers<br />");

      $sql = "SELECT ballotformpaper_status FROM ballotformpapers_web WHERE ballotformpaper_id='$serial' LIMIT 1";
      $res = $db->query($sql);

      if($debug) echo("queried db: $sql <br />");

      // No rows, then it doesn't exist
      if(mysql_num_rows($res) != 1) {
        $flagEnterSerial = true;
        $errMsg .= "<p>Could not find ballotform</p>";
        if($debug) echo("no rows<br />");
      } else {
        if($debug) echo("has rows<br />");

        // Exists, check status
        $arr = mysql_fetch_array($res,MYSQL_ASSOC);
        $status = $arr["ballotformpaper_status"];

        if($debug) echo("status: $status<br />");

        // If not status line doesn't contain 'voted', flag and return error.
        if(!strstr("audited",strtolower($status))) {
          $errMsg .= "<p>This ballot form has not been audited</p>";
          $flagEnterSerial = true;
          if($debug) echo("err: not audited<br />");

        }
      }

    } else {
      $flagEnterSerial = true;
      $errMsg .= "<p>Malformed serial number</p>";
      if($debug) echo("err: bad serial<br />");

    }
  } else {
    if($debug) echo("waiting for serial<br />");

    $flagEnterSerial = true;
  }


?><div id="mainlinks">
<a href="receiptlookup.php">Receipt Lookup</a><br />
<a href="auditedballot.php">Audited Ballot Lookup</a><br />
    </div>
    <div id="mainvider">
      <!-- nowt -->&nbsp;
    </div>
    <div id="maincontent">
      <div id="maintitle">Audited Ballot Lookup</div>
<?

  // if flagEnterSerial, provide input form for entering serial
  if($flagEnterSerial) {
    ?><h3>Serial Number</h3><?
    echo($errMsg);
    ?><form method=GET action="<? echo($_SERVER["PHP_SELF"]); ?>">
    <p>Please enter audited ballot form serial number:</p>
    <p><input type="text" name="serial" /><br />
    <input type=submit value="Retrieve audit report" /></p>
    </form><?

    // exit
    exit();
  }

  if($debug) echo("retrieving...<br />");

  // ************************************
  // Retrieve a list of tellerids
  $sql = "SELECT teller_id FROM tellers_web";
  $tellersArray = $db->queryArr($sql);

  // Retrieve the ballotform serial numbers from this ballotformpaper
  $sql = "SELECT * FROM ballotformsinpapers WHERE ballotformpaper_id=$serial";
  $ballotformsdata = $db->queryArr($sql);

  // For each ballotform
  foreach($ballotformsdata as $row => $rowArr) {

    echo("<h3>Race: $row </h3>\n");

    $position = $rowArr["position"];
    $ballotform_id = $rowArr["ballotform_id"];

    // Start with canonical ordering
    /** TODO: Check that $position is the same index for a given race as that in $races */
    $order = array();
    for($i=0;$i<$races[$position];$i++) {
      $order[$i] = $i;
    }

    // Avoid possibility that the tellers are in the wrong order
    sort($tellersArray);

    // start with 2d array to collapse later
    $csPreArr = array();
    foreach($order as $key=>$var) {
      $csPreArr[$key] = array();
    }

    // For each tellerid
    foreach($tellersArray as $key => $teller_id) {

      // For each 0,1
      for($batch = 0; $batch<2; $batch++) {

        // Retrieve ballotformaudits_web table object using the ballotformserialno, tellerid, 0/1
        $audit = new Rec("ballotformaudits_web");
	$audit->retrieveByManyIds(array("ballotform_serialno"=>$ballotform_id,
					"teller_id"=>$teller_id,
					"teller_batch"=>$batch));

        // Apply the permutation
        $permutation = $audit->get("audit_permutation_permutation");
        $order = permuteWithPipes($order,$permutation);

        // Show the new order
        echo("<p>$i:".implode(",",$order)."</p>");


        // add to csArr entry
        foreach($order as $pos=> $val) {
          // this is num $val, which is currently in position $pos
          $csPreArr[$val][] = $pos;
        }



        ob_flush();
        flush();
 
      }
    }

    // rows and columns
    $cols = count($tellersArray)*2;
    $rows = count($order);

    // create initial canonical (easy)
    $initialTDs = array();
    foreach($order as $key=>$val) {
      $initialTDs[$key] = $races_candidates[$key];
    }

    // create final as-ballot order.
    $finalTDs = array();
    foreach($order as $key=>$val) {
      $finalTDs[$key] = $races_candidates[$val];
    }

  }




  ?><p><a href="<? echo($_SERVER["PHP_SELF"]) ?>">Look up another</a></p>

  </div><?

include("footer.php");
?>