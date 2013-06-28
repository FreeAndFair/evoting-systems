<?php

  /** This script processes the request for a submitted vote status page
    * . Initiate session
    * . Log URN, URL, IP, timedatestamp
    * . check session variables, retrieve database table
    * . return to user 
    */

//include_once("db4.php");
//include_once("rv.php");
//include_once("config.php");

// Head of page
$titleprefix = "Remote Voting";
include("header.php");

?>
<div id="mainlinks">
  <br />
</div>

<div id="mainvider">
   <!-- nowt -->&nbsp;
</div>
<div id="maincontent">

<div id="maintitle">Remote Voting</div>
<h4>USSU Sabbatical Elections 2007</h4>
<p>Welcome to the Remote Voting entry point. Remote voting (for those who have registered to vote remotely) will be available when the election begins, around 10am Tuesday morning.</p>
<p>Please come back to this page after the election has started.</p>
</div>
<? include("footer.php"); ?>