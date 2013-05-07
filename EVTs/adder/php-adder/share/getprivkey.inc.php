<?php require_once 'header.inc.php' ?>
</head>
<body>

<?php include 'plugin.inc.php' ?>

<div>
  <script type="text/javascript" src="scripts/getprivkey.js">
  </script>
</div>

<div class="container">

<?php include 'sidebar.inc.php' ?>
<div class="mainContent">
<h1>Private Key Creation</h1>
<?php
if (isset($errors) && is_array($errors) && count($errors) > 0) {
    require_once 'error.inc.php';
    exit();
}
?>
    <p>You have successfully logged in to Adder as an <strong>authority</strong>. You may perform the following operations at this time:</p>
    <div class="form-login">
      <form id="submitKeyForm" name="getKeyForm" action="index.php" method="post">
        <input type="hidden" name="user" value="<?php echo $_SESSION['user_id'] ?>" />
        <input type="hidden" name="procedure" value="<?php echo $procedure ?>" />
        <input type="hidden" name="pubkeySubmitted" value="<?php echo $submit_count ?>" />
        <input type="hidden" name="privateKey" value="<?php echo $privkey; ?>" />
        <input type="hidden" id="authPubKey" name="authPubKey" />
        <input type="button" name="saveKey" value="Save Private Key" onClick="savePrivateKey()" />
        <p><em>Saves your portion of the private key to your computer.</em></p>
      </form>
      </div>
<?php include 'footer.inc.php' ?>
</div>


</div>

</body>

</html>
