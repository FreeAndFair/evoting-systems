<?php require_once 'header.inc.php' ?>
</head>
<body>
  <div class="container">
    <?php include 'sidebar.inc.php' ?>

    <div class="mainContent">
      <h1>User Vote</h1>

      <p>You have requested the encrypted vote of
      <strong><?php echo $voter;?></strong>.</p>
<?php if (isset($vote) && !empty($vote)) { ?>
      <?php
      //echo "The security code of this vote is: <strong>". str_replace("\n", "", $short_hash)."</strong>.";
      ?>
      <p>The encrypted vote is:</p>

      <div class="ciphertext">
<?php echo display_data($vote, "ADDER VOTE"); ?>
      </div>
<?php } else { ?>
      <p><strong>No vote for this user.</strong></p>
<?php } ?>
<?php include 'footer.inc.php' ?>
    </div>
  </div>
</body>
</html>
