<?php 
// ----------
$csv = $_GET["csv"];


  //simulate a slowish process 
  $exec_string = "curl http://131.227.68.245/index.php?csv=$csv";
  $handle = popen($exec_string,'r'); 
  $flagReturning = false;
  if(!$handle) {
    // Assume nothing worked, downgrade user
    echo("1,'Vote submission attempt failed. Please retry later.'");
  } else {
    sleep(1);
    while(!feof($handle)) {
      $buffer = fgets($handle);
      $all_buffer .= $buffer;
      if($flagReturning == false) {
        //echo("0,");
        $flagReturning = true;
        
      }
      echo "$buffer<!-- buf -->";
      ob_flush();
      flush();
    }
    pclose($handle);
  }
  //echo(",111111");
//-------------
?>