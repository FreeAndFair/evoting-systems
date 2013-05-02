<?php require_once 'header.inc.php' ?>
</head>
<body>

<?php include 'plugin.inc.php' ?>

<div>
  <script type="text/javascript" src="scripts/createpolynomial.js">
  </script>
</div>

<div class="container">
<?php include 'sidebar.inc.php' ?>
<div class="mainContent">
<h1>Secret Share Creation</h1>
<?php
if (isset($errors) && is_array($errors) && count($errors) > 0) {
    require_once 'error.inc.php';
    exit();
}
?>
<p>
    You have successfully logged in to Adder as an <strong>authority</strong>.
</p>
<p>You are now required 
    to create a secret share and submit some information to the server. 
    When you select the &quot;Generate Secret Share&quot; option, your browser will generate a
    unique secret share for you, and compute some information based on the public keys of
    all authorities who participated in the previous stage. This information will then 
    be sent to the server. In the next stage, you, along with all other authorities, 
    will use this information to compute private decryptions keys.
</p>
<p>When all authorities who have participated in this stage have 
    submitted their secret share, the next stage can begin. You can determine if the next
    stage has begun by selecting &quot;Procedures&quot; and then clicking on the status link
    next to the procedure name.
</p>

    <p>You can perform the following operations at this time:</p>
    <div class="form-login">
      <form id="createPolynomialForm" name="createPolynomialForm" action="index.php" method="post">
        <input type="hidden" id="user" name="user" value="<?php echo $_SESSION['user_id'] ?>" />
        <input type="hidden" id="procedure" name="procedure" value="<?php echo $procedure ?>" />
        <input type="hidden" id="polynomialSubmitted" name="polynomialSubmitted" value="<?php echo $submit_count ?>" />
        <input type="hidden" id="threshold" name="threshold" value="<?php echo "$threshold"; ?>" />
        <input type="hidden" id="keyStr" name="keyStr" value="<?php echo $key_str; ?>" />
        <input type="hidden" id="authPolynomial" name="authPolynomial" />
        <input type="hidden" id="gValues" name="gValues" />

        <input type="button" id="createPoly" name="createPoly" value="Generate Secret Share" onclick="createPolynomial()" />

        <p><em>Creates a secret share and sends the necessary information to the server.</em></p>
      </form>
      </div>

<?php include 'footer.inc.php' ?>
</div>

</div>

</body>

</html>
