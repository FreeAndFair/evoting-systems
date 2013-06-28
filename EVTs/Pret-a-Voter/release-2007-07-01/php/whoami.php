<?php 
/** Who am i?
  * USAGE: whoami.php?set=myname&get=hisname
  *  No query (just whoami.php) returns IP address of user.
  *  get=<somename> returns the IP address of <somename> according to the db
  *  set=<somename> sets the IP address of <somename> in the db
  *  returns 'cx' on database connection error,
  *          'ip' on unknown ip (if a set)
  *          'nm' on unknown name (if a get)
  *  if both set and get called, returns set error in preference to get result.
  *  
  */

include_once("db4.php");
include_once("config.php");

$get = $_GET['get'];
$set = $_GET['set'];
$ip = $_SERVER['REMOTE_ADDR'];

// In case of neither set or get, return IP
if(!$set && !$get) {
  if($ip) {
    echo("-".$_SERVER['REMOTE_ADDR']);
  } else {
    echo("ip");
  }
  exit();
}

if($set) {
  // Shenanigans protection
  if(!ctype_alnum($set)) die("ip");

  // Look it up - does it exist?
  $arr = $db->queryArr("SELECT COUNT(*) FROM iplookup WHERE name='$set' LIMIT 1");

  $result = $arr[0];
  //echo("result:$result");
  foreach($result as $key => $val) {
    $count = $val;
  }

  if($count != 1) {
    $sql = "INSERT INTO `iplookup` (`id`,`name`,`ip`) VALUES (NULL,'$set','$ip');";
  } else {
    $sql = "UPDATE `iplookup` SET `ip`='$ip' WHERE `name`='$set';";
  }

  $res = $db->query($sql);

  if(!$res) die("cx");
}

if($get) {
  // Shenanigans protection
  if(!ctype_alnum($get)) die("nm");

  // Look it up
  $arr = $db->queryArr("SELECT * FROM iplookup WHERE name='$get' LIMIT 1");

  if(!$arr) {
    die("cx");
  } else {
    $result = $arr[0];

    echo("+".$result["ip"]);
  }
}



?>