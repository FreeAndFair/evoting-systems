<?php

include_once("db.php");
include_once("config.php");
include_once("spittable.php");
include_once("functioncollection.php");
include_once("recclass4.php");

?><head>
<style type="text/css">
td {
	color:red;
	height:2em;
	width:7em;
	overflow:scroll;
	font-size:small;
	border:1px solid #eeeeee;
}

table {
	width:80%;
}
</style></head>
<body><?

if(!isset($_GET['tablename'])) {
  $tables = $db->queryArr("SHOW TABLES");
  foreach($tables as $key=>$tablearr) {
    //echo("key:$key:<br />");
    foreach($tablearr as $table => $var) {
      $tablenames[] = $var;
      echo("<a href='".$_SERVER['PHP_SELF']."?tablename=$var'>$var</a><br />");
    }
  }

} else {

  $tablename = $_GET['tablename'];
  echo("<h2>$tablename</h2>");
  if(isset($_GET['startindex'])) $startindex = $_GET['startindex'];
  $rec = new Rec($tablename);

  // get ids to retrieve
  $keyfield = $rec->getKeyName();

  $sql = "SELECT $keyfield from $tablename ";
  if(isset($startindex)) $sql .= "WHERE $keyfield>$startindex ";
  $sql .= "LIMIT 50";

  global $db;
  $ids = $db->queryArr($sql);
  
  ?><table border=0 style="border:1px solid black;"><tr><?
  foreach($megastructure[$tablename] as $name => $field) {
    echo("<th>".$field->get("desc")." ($name)</th>");
  }
  echo("</tr>\n");

  foreach($ids as $key=>$val) {
    foreach($val as $key2 => $val2) {
      $id = $val2;
    }
    $newrec = new Rec($tablename);
    $newrec->retrieveById($id);
    echo($newrec->getHTMLRow());
  }
  ?></table><?
}
  

?></body></html>