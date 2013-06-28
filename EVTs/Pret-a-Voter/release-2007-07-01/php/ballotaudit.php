<?php

/** ballotaudit.php
  * Looks up a ballot form that has been audited and retrieve the info
  */

  // includes
  include_once("config.php");


  // do head of html page



  $flagEnterSerial = false;

  // check if serial number has been given. if not, flagEnterSerial
  if(isset($_GET['serial'])) {
    $serial = no_nasties($_GET['serial']);

    if(ctype_digit($serial) && $serial) {
      // serial number has been given. check has been audited, if not, flagEnterSerial.

      $sql = "SELECT ballotformpaper_status FROM ballotformpapers WHERE ballotformpaper_id='$serial' LIMIT 1";
      $res = $db->query($sql);
      if(mysql_num_rows($res) != 1) {
        $flagEnterSerial = true;
        $errMsg .= "<p>Could not find ballotform</p>";
      } else {
        $arr = mysql_fetch_array($res,MYSQL_ASSOC);
        $status = $arr["ballotformpaper_status"];
        if(!strstr("audited",strtolower($status))) {
          $errMsg .= "<p>This ballot form has not been audited</p>";
          $flagEnterSerial = true;
        }
      }

    } else {
      $flagEnterSerial = true;
      $errMsg .= "<p>Malformed serial number</p>";
    }
  } else {
    $flagEnterSerial = true;
  }



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


  /** not flagEnterSerial, so we can retrieve the thing */
  // get ballotformpapers object
  $bfp = new Rec("ballotformpapers");


  // retrieve ballotformsinpapers with this ballotformpaper_id (7)
  $sql = "SELECT * FROM ballotformsinpapers WHERE ballotformpaper_id='$serial'";
  $res = $db->queryArr($sql);

  foreach($res as $row => $vals) {
    // for each ballotformsinpaper, retrieve ballotform (7)
    $position = $vals["position"];
    $bf_arr[$position] = $vals["ballotform_id"];

    // retrieve all the ballotformaudits for this ballotform (10)
    $sql = "SELECT * FROM ballotformaudits WHERE ballotform_serialno='".$vals["ballotform_id"];

    $audits = $db->queryArr($sql);

    $tables[$vals["position"]] = array();

    foreach($audits as $num => $audit) {
      /** TODO: RETRIEVE FROM DATABASE, get the permutation $permutation
        * to apply as a string "03241"; */
      $permutation = "201";

      /** TODO: RETRIEVE NUMBER OF CANDIDATES */
      $candidates = 3;

      // tables[race][col][row]
      $tables[$position][$num] = array();

      // so, there is the current list, $curlist, and I need to permute it with this audit
      $curlist = permute($curlist,$permutation);

      // for each ballotformaudit, add the column for this permutation
      for($i=0;$i<strlen($curlist);$i++) {
        $tables[$position][$num][$i] = "<td><runpermute>" . $curlist[$i] . "</runpermute><permute>" . $permutation[$i] . "</permute></td>";
      }

    }

    // write table from array
    foreach($tables as $position=>$table) {
    $html = "<table>\n";
      foreach($table as $col => $rows) {
        foreach($rows as $row => $val) {
          $htmlRows[$row] .= $val;
        }
      }
      $htmltable = "<table> <tr>" . implode("</tr><tr>",$htmlRows) . "</tr></table>\n";

      echo($htmltable);
      ob_flush();
      flush();
    }
  }

    
  // finish page

?>