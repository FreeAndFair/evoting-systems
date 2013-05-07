<?php require_once 'header.inc.php' ?>
</head>
<body>

<?php include 'plugin.inc.php' ?>

<div>
  <script type="text/javascript" src="scripts/decrypt.js">
  </script>
</div>

<div class="container">

<?php include 'sidebar.inc.php' ?>
<div class="mainContent">
<h1>Partial Decryption</h1>
<?php
if (isset($errors) && is_array($errors) && count($errors) > 0) {
    require_once 'error.inc.php';
    exit();
}
?>
    <div class="form-postnews">
    <p>The procedure is now complete. To complete your duties as an authority, you must 
now submit your partial decryption of the procedure total. The private key that you created
before the procedure will be used to decrypt a portion of the encrypted procedure result,
which has been downloaded. Only when a sufficient number of authorities have participated 
in this stage will the total be available for the public to see.</p>

    <p>Number of submitted votes: <strong><?php if ($num_votes == "") echo "0"; else echo $num_votes; ?></strong></p>

    <form id="decryptionForm" action="index.php" method="post">
      <input type="hidden" id="user" name="user" value="<?php echo $_SESSION['user_id'] ?>" />
      <input type="hidden" id="procedure" name="procedure" value="<?php echo $procedure ?>" />
      <input type="hidden" id="decryptionSubmitted" name="decryptionSubmitted" value="<?php echo $submit_count; ?>" />
      <input type="hidden" id="cipherSum" name="cipherSum" value="<?php echo trim(str_replace("\n", "", $cipher_sum)); ?>" />
      <input type="hidden" id="partialDecryption" name="partialDecryption" value="" />
      <div align="center"><input id="submitDecryption" name="submitDecryption" type="button" value="Submit decryption" onclick="decryptSum()" /></div>
    </form>
    </div>
<?php include 'footer.inc.php' ?>
</div>


</div>

</body>

</html>
