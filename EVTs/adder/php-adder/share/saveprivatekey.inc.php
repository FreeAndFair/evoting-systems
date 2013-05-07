<?php require_once 'header.inc.php' ?>
</head>

<body>
  <?php include 'plugin.inc.php' ?>
  <div>
    <script type="text/javascript" src="scripts/saveprivatekey.js">
    </script>
  </div>
  <div class="container">
    <?php include 'sidebar.inc.php' ?>

    <div class="mainContent">
      <h1>Save Private Key</h1>
<?php
if (isset($errors) && is_array($errors) && count($errors) > 0) {
    require_once 'error.inc.php';
    exit();
}
?>
      <p>You have successfully logged in to Adder as an
      <strong>authority</strong>.</p>

      <p>In the previous stage, each authority created a piece of
      information for you. These pieces of information have been
      downloaded. When you select the "Save Private Key" option,
      they will be aggregated to form your unique private
      decryption key. At the end of the procedure, you will use
      this key to submit your portion of the decryption of the
      procedure total.</p>

      <p>When all authorities who have participated in this stage
      have created and saved their private keys, the next stage can
      begin. You can determine if the next stage has begun by
      selecting "Procedures" and then clicking on the status link
      next to the procedure name.</p>

      <p>You can perform the following operations at this time:</p>

      <div class="form-login">
        <form id="savePrivateKeyForm" name="savePrivateKeyForm"
        action="index.php" method="post">
          <input type="hidden" id="user" name="user" value=
          "<?php echo $_SESSION['user_id'] ?>" />
          <input type="hidden" id="procedure" name="procedure" value=
          "<?php echo $procedure ?>" />
          <input type="hidden" id="privKeyComponents"
          name="privKeyComponents" value=
          "<?php echo $private_key_components ?>" />
          <input type="hidden" id="privateKeySaved" name="privateKeySaved"
          value="true" />
          <input type="button" id="saveKey" name="saveKey"
          value="Save Private Key" onclick="savePrivateKey()" />

          <p><em>Saves the private key in your home
          directory.</em></p>
        </form>
      </div>
<?php include 'footer.inc.php' ?>
    </div>
  </div>
</body>
</html>
