<?php 


include_once("config.php");

// test ballotcreate
$titleprefix = "Test Ballot Display";
include_once("header.php");


// $boxesdata[ballotnum][line]   (ballotnum:- 0 to races-1, line:- 1 to $candidates)
// function ballotHTML($boxesdata)
$boxesdata = array();

$boxesdata[0] = array( 	1=>"a1",
			2=>"a2",
			3=>"a3");

$boxesdata[1] = array( 	1=>"b1",
			2=>"b2");

$boxesdata[2] = array( 	1=>"c1",
			2=>"c2",
			3=>"c3");

$boxesdata[3] = array( 	1=>"d1",
			2=>"d2");

$boxesdata[4] = array( 	1=>"e1",
			2=>"e2");


$boxesdata[5] = array( 	1=>"x1",
			2=>"x2");


$boxesdata[6] = array( 	1=>"y1",
			2=>"y2");

echo ballotHTML($boxesdata);

include("footer.php");

?>