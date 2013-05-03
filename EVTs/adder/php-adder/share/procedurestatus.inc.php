<?php require_once 'header.inc.php' ?>
</head>
<body>

<div class="container">

<?php include 'sidebar.inc.php' ?>
<div class="mainContent">
<h1>Procedure Status</h1>
<?php
if (isset($errors) && is_array($errors) && count($errors) > 0) {
    require_once 'error.inc.php';
    exit();
}
?>
<h2>Procedure Information</h2>
<p><strong>Title:</strong> <?php echo isset($_GET['title']) ? stripslashes($_GET['title']) : "" ?></p>
<p><strong>Type:</strong> Choose <?php echo $min ?> out of <?php echo $max ?></p>
<p><strong>Ballot question:</strong> <?php echo stripslashes($question) ?><br /></p>

<p><strong>Choices:</strong></p>
<ul>
<?php
if (isset($candidates) && is_array($candidates)) {
    foreach ($candidates as $choice) {
        $c = str_replace("\'", "'", $choice[1]);
        $c = str_replace('\"', '"', $c);
        echo "<li>$c</li>\n";
    }
}
?>
</ul>

<p><strong>Stage:</strong> <?php echo $stage_descr; ?>.</p>
<p><strong>Deadline:</strong> <?php echo $deadline; ?></p>

<?php
$server = new AdderInterface();
$server->connect(DEFAULT_SERVER);
$procedure = $_GET['procedure'];
if ($server->get_stage($procedure) == ADDER_STAGE_FINISHED) {
    ?>
 <h2>Results</h2>
<div>
     <table summary="Results">
      <thead>
      <tr><th align="left">Choice</th><th align="center">Votes</th></tr>
      </thead>
      <tbody>

<?php
    $results = $server->get_results($procedure);
    $results_array = explode("\n", $results);
    $results_array = array_diff($results_array, array(""));
 
    $maximum = 0;

    foreach ($results_array as $item) {
        $fields = preg_split("/'/", $item, -1, PREG_SPLIT_NO_EMPTY);
     
        if ($fields[1] > $maximum) {
            $maximum = $fields[1];
        }
    }

    foreach ($results_array as $item) {
        $fields = preg_split("/'/", $item, -1, PREG_SPLIT_NO_EMPTY);

        if ($fields[1] == $maximum) {
            echo '<tr><td align="left" style="color: red"><em>' . $fields[0] . '</em></td><td align="center" style="color: red"><em>' . $fields[1] . '</em></td></tr>' . "\n";
        } else {
            echo '<tr><td align="left">' . $fields[0] . '</td><td align="center">' . $fields[1] . '</td></tr>' . "\n";
        }
    }
?>
</tbody>
</table>
</div>
<?php
}
?>
<?php
$server->disconnect();
?>

<?php include 'footer.inc.php' ?>
</div>
</div>

</body>

</html>
