<?php require_once 'header.inc.php' ?>
</head>
<body>

<?php include 'plugin.inc.php' ?>

<div>
  <script type="text/javascript" src="scripts/vote.js">
  </script>
</div>

<div class="container">

<?php include 'sidebar.inc.php' ?>
<div class="mainContent">
<h1>Vote Selection</h1>
<?php
if (isset($errors) && is_array($errors) && count($errors) > 0) {
    require_once 'error.inc.php';
    exit();
}
?>
<?php 
/* FIXME: This all needs to go in index.php */
$server = new AdderInterface();
$server->connect(DEFAULT_SERVER);
$desc = stripslashes($server->get_description($_GET["procedure"]));
$procedure = $_GET['procedure'];
$votes = $server->get_choices($procedure);
$num_choices = $server->get_num_choices($procedure);
$procedures = $server->get_procedure_list();
$min = $procedures[$procedure]['min'];
$max = $procedures[$procedure]['max'];
$num = $num_choices[1];
#$min = isset($num_choices[2]) ? $num_choices[2] : 1;
#$max = isset($num_choices[3]) ? $num_choices[3] : 1;
$server->disconnect();
?>
    <p>You have logged into Adder as a <strong>voter</strong>. Please fill in the ballot below, and 
select "Submit Encrypted Vote" to review and submit your vote.</p>

<div class="ballot">
  <p align="center"><strong><span class="question"><?php echo $desc ?></span></strong></p>
  <form id="securityForm" action="index.php" method="post">
    <input type="hidden" id="user" name="user" value="<?php echo $_SESSION['user_id'] ?>" />
    <input type="hidden" id="procedure" name="procedure" value="<?php echo $procedure ?>" />
    <input type="hidden" id="voteSubmitted" name="voteSubmitted" value="<?php echo $submit_count ?>" />
    <input type="hidden" id="num" name="num" value="<?php echo $num ?>" />
    <input id="serverPublicKey" name="serverPublicKey" type="hidden"
    value="<?php echo $pubkey ?>" />
    <input id="min" name="min" type="hidden" value="<?php echo $min ?>" />
    <input id="max" name="max" type="hidden" value="<?php echo $max ?>" />
<?php
if (isset($votes) && !empty($votes)) {
$i = 0;
echo '<div align="center">' . "\n";
$choices = ($min == 1 ? "choice" : "choices");
if ($min == $max) {
    echo '<p><em>Select exactly ' . $min . ' ' . $choices . '</em></p>' . "\n";
} else {
    echo '<p><em>Select between ' . $min . ' and ' . $max . ' ' . $choices . '</em></p>' . "\n";
}

foreach ($votes as $vote) {
    echo '<input type="checkbox" id="vote' . $i . '" name="vote" value="' . $vote[0] . '" onclick="checkBox(this)" /><label for="vote' . $i . '">' . stripslashes($vote[1]) . '</label><br />' . "\n";
    $i++;
}
echo '</div>' . "\n";
}
?>
    <input id="encryptedVote" name="encryptedVote" type="hidden" /><br />
    <div align="center">
      <input id="submitVote" name="submitVote" type="button" value="Submit Encrypted Vote"
      onclick="encryptVote()" />
      <input id="reset" name="reset" type="reset" /></div>
  </form>
</div>
<?php include 'footer.inc.php' ?>
</div>

</div>

</body>

</html>
