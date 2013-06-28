<?php

include("db.php");
include("config.php");
include("spittable.php");
include("functioncollection.php");

?><head>
<style type="text/css">
td {
	color:red;
	height:2em;
	width:7em;
	overflow:scroll;
	font-size:x-small;
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
  spitTable($_GET['tablename']);
}
  

?></body></html>