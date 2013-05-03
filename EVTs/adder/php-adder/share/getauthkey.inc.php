<?php require_once 'header.inc.php' ?>
</head>	
<body>

  <div class="container">
    <?php include 'sidebar.inc.php' ?>

    <div class="mainContent">
      <h1>Authority Public Key</h1>

      <p>You have requested the public key of <strong><?php echo $auth_id; ?></strong>. 
<?php if (isset($pubkey) && !empty($pubkey)) { ?>
      The public key is:</p>
<div class="ciphertext">
<?php echo display_data($pubkey, "ADDER PUBLIC KEY"); ?>
</div>
<?php } else { ?>
      <p><strong>No key for this user.</strong></p>
<?php } ?>

      <?php include 'footer.inc.php' ?>
  </div>
</div>
</body>
</html>
