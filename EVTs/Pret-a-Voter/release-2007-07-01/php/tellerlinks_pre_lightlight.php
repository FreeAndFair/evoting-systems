<?php

/** tellerlinks.php
  * This page looks up a teller's L/R links, given the teller id
  **/

  // includes
  include_once("config.php");

  // Get the debug switch
  if(isset($_GET['debug'])) {
    $debug = $_GET['debug'];
  } else {
    $debug = 0;
  }

  // do head of html page
  $titleprefix = "Teller Links Lookup";
  if($debug) $titleprefix .= " - debug";
  include("header.php");


  $flagEnterSerial = false;

  // check if serial number has been given. if not, flagEnterSerial
  if(isset($_GET['tellerid']) && isset($_GET['raceid']) && isset($_GET['electionid'])) {
    $serial = no_nasties($_GET['tellerid']);

    if($debug) echo("have teller id etc<br />");
    if(ctype_digit($tellerid)
	&& ctype_digit($raceid) 
	  && ctype_digit($electionid)) {

      // serial number has been given. check has been audited, if not, flagEnterSerial.
      if($debug) echo("it has numbers<br />");
/**************
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
*/
    } else {
      $flagEnterTellerid = true;
      $errMsg .= "<p>Malformed teller id</p>";
      if($debug) echo("err: bad teller_id<br />");

    }
  } else {
    if($debug) echo("waiting for teller id<br />");

    $flagEnterSerial = true;
  }


?><div id="mainlinks">
<a href="receiptlookup.php">Receipt Lookup</a><br />
<a href="auditedballot.php">Audited Ballot Lookup</a><br />
<a href="tellerlinks.php">Teller Links Lookup</a><br />
    </div>
    <div id="mainvider">
      <!-- nowt -->&nbsp;
    </div>
    <div id="maincontent">
      <div id="maintitle">Audited Ballot Lookup</div>
<?

  // if flagEnterSerial, provide input form for entering serial
  if($flagEnterSerial) {
    ?><h3>Teller Selection</h3><?
    echo($errMsg);

    $sql = "SELECT teller_id FROM tellers";
    $resArr = $db->queryArr($sql);

    //$tellers = array();
    foreach($resArr as $num=>$result) {
      $teller = $result["teller_id"];

      echo("<b>Teller ".$teller."</b> links, in: ");
      foreach($racesArr as $race => $val) {
	echo("<a href='".$_SERVER["PHP_SELF"]."?tellerid=".
		$teller."&raceid=".$race."&electionid=0'>Race $race</a>&nbsp;&nbsp;");
      }
      echo("<br />\n");

    }

    

    // exit
    exit();
  }

  if($debug) echo("retrieving...<br />");

  /** TODO: GUTS GO HERE */





  ?><p><a href="<? echo($_SERVER["PHP_SELF"]) ?>">Look up another</a></p>

  </div><?

include("footer.php");
?>