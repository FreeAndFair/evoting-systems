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
include_once("lightlightinclude.php");
include_once("headerB.php");


    $nth = array( 0=>'First', 1=>'Second', 2=>'Third' );


  // Get the debug switch
  if(isset($_GET['debug'])) {
    $debug = $_GET['debug'];
  } else {
    $debug = 0;
  }

  // These TDs arrays will hold the actual names of the candidates. 
  //$initialTDs;
  //$finalTDs; 

  // do head of html page
  $titleprefix = "Audited Ballot Lookup";
  if($debug) $titleprefix .= " - debug";

  writeheadA();


  $flagEnterSerial = false;

  // check if serial number has been given. if not, flagEnterSerial
  if(isset($_GET['serial'])) {
    $serial = no_nasties($_GET['serial']);

    //if($debug) echo("have serial<br />");
    if(ctype_digit($serial) && $serial) {

      // serial number has been given. check has been audited, if not, flagEnterSerial.
      //if($debug) echo("it has numbers<br />");

      $sql = "SELECT ballotformpaper_status FROM ballotformpapers WHERE ballotformpaper_id='$serial' LIMIT 1";
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




  // if flagEnterSerial, provide input form for entering serial
  if($flagEnterSerial) {
  writeheadB();
writeheadC();
?><div id="mainlinks">
<a href="receiptlookup.php">Receipt Lookup</a><br />
<a href="auditedballot.php">Audited Ballot Lookup</a><br />
<a href="tellerlinks.php">Teller Links Audit</a><br />
<a href="tally.php">Election Tally</a><br />
    </div>
    <div id="mainvider">
      <!-- nowt -->&nbsp;
    </div>
    <div id="maincontent">
      <div id="maintitle">Audited Ballot Lookup</div>
<?

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

  
 if(!isset($_GET['ballotformid'])) {
   writeheadB();
    writeheadC();

?><div id="mainlinks">
<a href="receiptlookup.php">Receipt Lookup</a><br />
<a href="auditedballot.php">Audited Ballot Lookup</a><br />
<a href="tellerlinks.php">Teller Links Audit</a><br />
<a href="tally.php">Election Tally</a><br />
   </div>
    <div id="mainvider">
      <!-- nowt -->&nbsp;
    </div>
    <div id="maincontent">
      <div id="maintitle">Audited Ballot Lookup</div>
<?


    // Retrieve the ballotform serial numbers from this ballotformpaper
    $sql = "SELECT ballotform_id,position FROM ballotformsinpapers WHERE ballotformpaper_id=$serial";
    $ballotformsdata = $db->queryArr($sql);

    foreach($ballotformsdata as $row=>$rowArr) {
      $ballotformid = $rowArr["ballotform_id"];
      $position = $rowArr["position"];
      echo("<a href='".$_SERVER["PHP_SELF"]."?serial=$serial&ballotformid=$ballotformid'>View ".strtolower($nth[$position])." race for '".$race_titles[$position]."' ($ballotformid)</a><br />\n");
    }
 ?><p><a href="<? echo($_SERVER["PHP_SELF"]) ?>">Look up another</a></p>

  </div><?

include("footer.php");

   exit();
    //}

  }

   writelightlightstyles();
   writeheadB();

    $ballotformid = $_GET['ballotformid'];

    $ballotobj = new Rec("ballotforms");
    $ballotobj->retrieveById($ballotformid);


    if($debug) echo("retrieving...<br />");
  
    // ************************************
    // Retrieve a list of tellerids
    $sql = "SELECT teller_id FROM tellers";
    $tellersRes = $db->queryArr($sql);

    $tellersArray = array();
    foreach($tellersRes as $row => $data) {
      $tellersArray[$row] = $data["teller_id"];
    }

    // rows and columns
    $cols = count($tellersArray)*2+1;
    $rows = $racesArr[$ballotobj->get("race_id")];

   writelightlightheadscript($rows,$cols);
   writeheadC();

?><div id="mainlinks">
<a href="receiptlookup.php">Receipt Lookup</a><br />
<a href="auditedballot.php">Audited Ballot Lookup</a><br />
<a href="tellerlinks.php">Teller Links Audit</a><br />
<a href="tally.php">Election Tally</a><br />
    </div>
    <div id="mainvider">
      <!-- nowt -->&nbsp;
    </div>
    <div id="maincontent">
      <div id="maintitle">Audited Ballot Lookup</div>
<?

  $thisballot = $ballotobj; //new Rec("ballotforms");
  //$thisballot->retrieveById($serial);
  $racenum = $thisballot->get("race_id");
  //$numcandidates = $candidates[$racenum];
  $numcandidates = $racesArr[$racenum];
  if($debug) echo("this is race $racenum<br />\n");

  echo("<p>Audited Ballot Result for ".strtolower($nth[$racenum])." race on ballot paper $serial: <br /><b>'".$race_titles[$racenum]."'</b></p>\n");

  //if($debug) print_r($ballotformsdata);


  //foreach($ballotformsdata as $row => $rowArr) {

    //$position = $rowArr["position"];
    //$ballotform_id = $rowArr["ballotform_id"];
    


    // Start with canonical ordering
    /** TODO: Check that $position is the same index for a given race as that in $racesArr */
    $order = array();
    for($i=0;$i<$racesArr[$racenum];$i++) {
      $order[$i] = $i;
    }

    // Avoid possibility that the tellers are in the wrong order
    sort($tellersArray);

    if($debug) print_r($tellersArray);

    // start with 2d array to collapse later
    $csPreArr = array();
    foreach($order as $key=>$var) {
      $csPreArr[$key] = array();
    }

    if($_GET['test'] == 1) {
      $testperm = array( 0=>"1|2|3|4|5",1=>"2|3|4|5|6|1", 2=>"1|2");
    }

    foreach($order as $pos=> $val) {
      // this is num $val, which is currently in position $pos
      $csPreArr[$val][] = $pos;
    }

    // For each tellerid
    //foreach($tellersArray as $key => $teller_id) {
    for($key=0;$key<count($tellersArray);$key++) {
    //for($key=count($tellersArray)-1;$key>=0;$key--) {
      $teller_id = $tellersArray[$key];

      if($debug) echo("Running for <b>teller $teller_id:</b><br />\n");

      // For each 0,1
      //for($batch = 0; $batch<2; $batch++) {
      for($batch = 1; $batch>=0; $batch--) {


        if($debug) echo("...<b>batch $batch</b><br />\n");

        //echo("serial: $ballotformid, teller: $teller_id, batch: $batch, ");

        // Retrieve ballotformaudits table object using the ballotformserialno, tellerid, 0/1
        $audit = new Rec("ballotformaudits");
	$audit->retrieveByManyIds(array("ballotform_serialno"=>$ballotformid,
					"teller_id"=>$teller_id,
					"teller_batch"=>$batch));

        // Apply the permutation
        $permutation = $audit->get("audit_plaintext_permutation");

        if($_GET['test'] == 1) $permutation = $testperm[$racenum];
        if($debug) {
		echo("Order before permute: ");
		print_r($order);
		echo("<br />\n");
		echo("permutation: $permutation");
		echo("<br />\n");
	}

        $order = permuteWithPipes($order,$permutation);

        //echo("order: ".implode(",",$order).", after perm: $permutation<br />\n");

        // Show the new order
        if($debug) echo("<p>$teller_id,$batch:".implode(",",$order)."</p>");


        // add to csArr entry
        foreach($order as $pos=> $val) {
          // this is num $val, which is currently in position $pos
          $csPreArr[$val][] = $pos;
        }



        ob_flush();
        flush();
 
      }
    }

    //echo("csPreArr:<br />\n");
    //print_r($csPreArr);

    $csArr = array();
    foreach($csPreArr as $group => $arr) {
      $csArr[$group] = implode(",",$arr);
    }

    /*echo("<h3>Initial order:</h3>");
    // create initial canonical (easy)
    $initialTDs = array();
    foreach($order as $key=>$val) {
      $initialTDs[$key] = $races_candidates[$racenum][$key];
      echo($races_candidates[$racenum][$key]."<br />\n");
    } //COMMENTED OUT BY DAVID */

    //print_r($order);

    echo("<h3>Final order:</h3>");

    // create final as-ballot order.
    $finalTDs = array();
    foreach($order as $key=>$val) {
      $finalTDs[$key] = $races_candidates[$racenum][$val];
      echo($races_candidates[$racenum][$val]."<br />\n");
    }

    //print_r($finalTDs);
    echo("<h3>Visualisation:</h3>");

    echo("<p>Below is a visual representation of the permutation data</p>\n");

    writelightlightbody($csArr);

 // }




  ?><p><a href="<? echo($_SERVER["PHP_SELF"]) ?>">Look up another</a></p>

  </div><?

include("footer.php");
?>