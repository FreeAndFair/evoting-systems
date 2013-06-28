<?php 

// test link page

include_once("config.php");
include_once("lightlightinclude.php");
include_once("headerB.php");

writeheadA();


/******* some stuff goes here to calculate rows and cols */
$rows = 10;
$cols = 3;

writelightlighthead($rows,$cols);
writeheadB();

?><div id="mainlinks">
<a href="receiptlookup.php">Receipt Lookup</a><br />
<a href="auditedballot.php">Audited Ballot Lookup</a><br />
<a href="tally.php">Election Tally</a><br />
    </div>
    <div id="mainvider">
      <!-- nowt -->&nbsp;
    </div>
    <div id="maincontent">
      <div id="maintitle">Show Links</div>
<?

/******** some stuff goes here to generate the big csArray */
$csArr = array();
$csArr[] = "1,4,";
$csArr[] = ",2,3";


writelightlightbody($csArr);


include("footer.php");

?>