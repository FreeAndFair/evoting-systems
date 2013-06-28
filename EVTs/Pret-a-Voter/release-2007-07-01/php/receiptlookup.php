<?php 

/** receiptlookup.php
  * The receipt lookup takes a serial number as an argument (serial=),
  *  and returns a nicely formatted html page of the receipt.  */

  // includes
  include_once("config.php");

  // Get the debug switch
  if(isset($_GET['debug'])) {
    $debug = $_GET['debug'];
  } else {
    $debug = 0;
  }

  // do head of html page
  $titleprefix = "Receipt Lookup";
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

      // reform it into an integer - useful if people type in 000063 instead of 63:
      $serial = intval($serial);

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
        if(!strstr("voted",strtolower($status))) {
          $errMsg .= "<p>This ballot form has not been voted with</p>";
          $flagEnterSerial = true;
          if($debug) echo("err: not voted with<br />");

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
<a href="tellerlinks.php">Teller Links Audit</a><br />
<a href="tally.php">Election Tally</a><br />
    </div>
    <div id="mainvider">
      <!-- nowt -->&nbsp;
    </div>
    <div id="maincontent">
      <div id="maintitle">Receipt Lookup</div>
<?

  // if flagEnterSerial, provide input form for entering serial
  if($flagEnterSerial) {
    ?><h3>Serial Number</h3><?
    //echo($errMsg);
    ?><form method=GET action="<? echo($_SERVER["PHP_SELF"]); ?>">
    <p>Please enter voted ballot form serial number:</p>
    <p><input type="text" name="serial" /><br />
    <input type=submit value="Retrieve receipt" /></p>
    </form>

  </div><?

include("footer.php");

    // exit
    exit();
  }

  if($debug) echo("retrieving...<br />");

  // get ballotforms using the ballotformpapers_id
  $sql = "select ballotform_id,position from ballotformsinpapers where ballotformpaper_id=$serial";
  $forms = $db->queryArr($sql);

  if($debug) print_r($forms);

  //in order to test the next section, pretend we have some numbers
  $testids = array( 0=>"1", 1=>"2", 2=>"3"  );

  $formids = array();
  $formsdata = array();
  $votearr= array();
  foreach($forms as $form => $data) {
    $pos = $data["position"];
    $id = $data["ballotform_id"];
    if($debug) echo("pos: $pos, id: $id<br />\n");
    if($_GET['test']==1) $id=$testids[$pos];
    //echo("id:$id<br />");
    $formids[$pos] = $id;
    $rec = new Rec("ballotforms");
    $rec->retrieveById($id);
    $formsdata[$pos] = $rec;
    //echo("id:$id, pos:$pos");
    //print_r($rec);
    $votearr[] = $rec->get("ballotform_plaintext_vote");
    /** TODO: NOT WORKING ^ */
  }

  $votestring = implode(",",$votearr);
  if($debug) echo("VOTESTRING:$votestring<br />\n");

  sort($formids);

  //print_r($formsdata);


  // look up receipt data, for pretty hash
  $receipt = new Rec("ballotformpapers");
  if($debug) echo("rec made, requesting...<br />");
  $receipt->retrieveById($serial);
  


  if($debug) echo("...finished<br />");

  ?>Receipt for vote with serial number <?
  echo($serial) ?>, hash mark below:
  <p align=center><? 

  /** unneeded section after change around for mk2
  // retrieve vote string
  $receiptvotestring = $votestring; //$receipt->get("ballotformpaper_vote");
    */

  // retrieve pretty hash, replacing <br /> for \
  $receiptprettyhash = implode("<br />\n",explode("\\",$receipt->get("ballotformpaper_plaintext_hash")));

  // print pretty hash
  echo($receiptprettyhash);

  ?></p><?

  // put receiptvotes in usable array
  $receiptvotes = $votearr; //explode(",",$receiptvotestring);
  
  /**  ***** Fill the boxesdata array **************** */
  $boxesdata = array();

  global $racesArr;

//   echo("number of races: ".count($racesArr)."<br />\n");

  foreach($racesArr as $race=>$candidates) {
   
    /* example:
     * $boxesdata[0] = array( 	1=>"a1",
				2=>"a2",
				3=>"a3");  */

    $boxesdata[$race] = array();
    $thisarr = explode("|",$receiptvotes[$race]); 

    for($i=1;$i<=$candidates;$i++) {
      $thisval = $thisarr[$i-1];

      /** TODO: Do any kind of processing, like converting to image version 
        *    -> translateVoteMarks func (in collection) */
      $htmlcontents = translateVoteMarks($thisval);

      $boxesdata[$race][$i] = "$htmlcontents";
    }

  }

  // spit out all the HTML for this ballot form
  echo ballotHTML($boxesdata);

  ?><p><a href="<? echo($_SERVER["PHP_SELF"]) ?>">Retrieve another receipt</a></p>

  </div><?

include("footer.php");
?>