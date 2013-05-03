<?php require_once 'header.inc.php' ?>
</head>

<body>
  <div class="container">
    <?php include 'sidebar.inc.php' ?>

    <div class="mainContent">
      <h1>Proof of Ballot Validity</h1>

      <p>You have requested the ballot proof of
      <strong><?php echo $bp; ?></strong>.</p>
<?php if (isset($ballot_proof) && !empty($ballot_proof)) { ?>
      <p>The ballot proof is:</p>

      <div class="ciphertext">
<?php echo display_data($ballot_proof, "ADDER BALLOT PROOF"); ?>
      </div>
<?php } else { ?>
      <p><strong>No ballot proof for this user.</strong>
<?php } ?>
<?php include 'footer.inc.php' ?>
    </div>
  </div>
</body>
</html>
