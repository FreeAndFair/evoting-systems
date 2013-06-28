<?php

/ ** Further Info Page
   * This page receives some information about a record, retrieves
   *   the record, and returns the data in a nice format.
   */

// $furtherinfopage?table=$oftable&highlight=$value

global $db;

$table = $_GET['table'];
$highlight = $_GET['highlight'];

// Do some checks to prevent silliness or maliciousness
$strchk = strtolower($table.$highlight.$field);

if(  (strlen($strchk) > 70)
   || (strlen($strchk) < 4)
   || (strstr($strchk),'drop') 
   || (strstr($strchk),'insert')
   || (strstr($strchk),'update')  )  die("Malformed table name");

$rec = new Rec($table);
$rec->retrieveById($highlight);

echo("