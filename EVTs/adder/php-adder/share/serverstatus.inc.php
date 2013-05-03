<?php require_once 'header.inc.php' ?>
</head>
<body>

<div class="container">

<?php include 'sidebar.inc.php' ?>
<div class="mainContent">
<div class="titleRow"><img class="titleImage" src="images/adder-small-0.1.png" alt="Small Adder" /> <span class="titleText"><img src="images/banner.png" alt="Adder banner" /></span></div>
<h1>Active Procedures</h1>
<?php
function cmp($a, $b)
{
   $a = $a[1];
   $b = $b[1];
   return strcasecmp($a, $b);
}

if (isset($procedures) && is_array($procedures) && count($procedures) > 0) {
    usort($procedures, "cmp");

    foreach ($procedures as $procedure) {
        if ($procedure["stage"] != ADDER_STAGE_NOTSTARTED) {
            $query_string = "procedure=" . urlencode($procedure["id"]);
            echo $procedure["title"] . " (<a href=\"status.php?"
                . htmlentities($query_string) . "\">Status</a>)<br />";
        }
    }
} else {
    echo "<p>There are no active procedures.</p>\n";
}
?>
</div>
</div>
</body>
</html>
