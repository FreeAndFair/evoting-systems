<?php require_once 'header.inc.php' ?>
</head>

<body>
  <?php include 'plugin.inc.php' ?>

  <div>
    <script type="text/javascript" src="scripts/createkey.js">
    </script>
  </div>

  <div class="container">
    <?php include 'sidebar.inc.php' ?>

    <div class="mainContent">
      <h1>Key Creation</h1>
<?php
if (isset($errors) && is_array($errors) && count($errors) > 0) {
    require_once 'error.inc.php';
    exit();
}
?>
      <p>You have successfully logged in to Adder as an
      <strong>authority</strong>.</p>

      <p>You are now required to create a private keypair and
      submit your public key to the server. When you select the
      "Create Private Keypair" option, a public key and private key
      will be created and stored on your system. It is important
      that you do not share this private key with anyone. When you
      click "Submit Public Key", your public key will be submitted
      to the server.</p>

      <p>When all authorities who have participated in this stage
      have submitted their public keys, the next stage can begin.
      You can determine if the next stage has begun by selecting
      "Procedures" and then clicking on the status link next to the
      procedure name.</p>

      <p><strong>Caution:</strong> Do not select "Create Private
      Keypair" if you have already submitted a public key. It will
      erase your existing private key.</p>

      <p>You can perform the following operations at this time:</p>

      <div class="form-login">
        <form id="createKeyForm" name="createKeyForm" action=
        "index.php" method="post">
          <input type="hidden" id="user" name="user" value=
          "<?php echo $_SESSION['user_id']; ?>" />
          <input type="hidden" id="procedure" name="procedure"
          value="<?php echo $procedure ?>" />
          <input type="hidden" id="pubkeySubmitted"
          name="pubkeySubmitted" value=
          "<?php echo $submit_count ?>" />
          <input type="hidden" id="keyConstants" name="keyConstants" value=
          "<?php echo $key_constants ?>" />
          <input type="hidden" id="authPubKey" name="authPubKey" />
          <input type="button" id="createKey" name="createKey" value=
          "Create Private Keypair" onclick="createKeyPair()" />

          <p><em>Creates a private key pair and stores it in your
          home directory.</em></p>

          <input type="button" id="submitKey" name="submitKey" value=
          "Submit Public Key" disabled="disabled"
          onclick="readPubKey()" />

          <p><em>Submits your public key to the Adder
          server.</em></p>
        </form>
      </div>
      <?php include 'footer.inc.php' ?>
    </div>
  </div>
</body>
</html>
