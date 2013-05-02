<?php require_once 'header.inc.php' ?>
  <script type="text/javascript" src="scripts/login.js">
  </script>
</head>
<body>
<?php include 'plugin.inc.php' ?>
<div class="container">
<?php include 'sidebar.inc.php' ?>
<div class="mainContent">
<h1>Procedure Login</h1>
<?php
if (isset($errors) && is_array($errors) && count($errors) > 0) {
    require_once 'error.inc.php';
    exit();
}
?>
<p>Enter your username and password to be logged into the procedure you have selected.</p>
    <form id="loginForm" action="index.php?procedure=<?php echo $procedure; ?>" method="post">
<div class="row">
    <input type="hidden" id="loginSubmitted" name="loginSubmitted" value="<?php echo (is_numeric($submit_count) ? $submit_count : 1); ?>" />
</div>

    <div class="loginform">

    <div class="row">
    <span class="label">User ID:</span>
    <span class="formw"><input type="text" id="user" name="user" size="15" maxlength="15" onchange="validateUsername(this)" /></span><br />
    </div>

    <div class="row">
    <span class="label">Password:</span>
    <span class="formw"><input type="password" id="password" name="password" size="15" maxlength="15" onchange="validatePassword(this)" /></span><br />
    </div>

    <div class="row formbuttons">
    <input type="submit" id="login" name="login" value="Login" onclick="validateAll()" />
    <input id="reset" type="reset" />
    </div>
    </div>

    </form>
<?php include 'footer.inc.php' ?>
</div>

</div>

</body>

</html>
