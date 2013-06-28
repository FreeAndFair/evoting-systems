<?php


function spitTable($tablename) {
  global $db;

  $res = $db->queryArr("SELECT * FROM $tablename LIMIT 50");

  ?><table border=1><?
  // get column headers
  $arr = $res[0];
  ?><tr><td>Row</td><?
  foreach($arr as $field=>$val) {
    echo("<th>$field</th>");
  }
  ?></tr>
<?
  foreach($res as $row=>$arr) {
    echo("<tr><td><b>$row</b></td>");
    foreach($arr as $key=>$value) {
      if(strlen($value)>50) {
        echo("<td><a href='getfield.php'>get</a></td>");
      } else {
        echo("<td>$value</td>");
      }
    }
    echo("</tr>");
  }
  ?></table><?

  return true;
}

?>