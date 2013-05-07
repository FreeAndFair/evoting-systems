<?php require_once 'header.inc.php' ?>
</head>

<body>
  <div>
    <script type="text/javascript" src="scripts/makeuser.js">
    </script>
  </div>

  <div class="container">
    <?php include 'sidebar.inc.php' ?>

    <div class="mainContent">
      <h1>Add New User</h1>
<?php
if (isset($errors) && is_array($errors) && count($errors) > 0) {
    require_once 'error.inc.php';
    exit();
}
?>

<p>Enter a username and password to create a new user.</p>
 
<div>
<form id="createUserForm" action="index.php" method="post">
<div class="loginform">
    <div class="row">
    <input type="hidden" id="createUserSubmitted" name="createUserSubmitted" value="<?php echo (isset($submit_count) && is_numeric($submit_count) ? $submit_count : 1); ?>" />
    </div>

    <div class="row">
    <span class="label">User ID:</span>
    <span class="formw"><input type="text" id="user" name="user" size="15" maxlength="15" /></span><br />
    </div>

    <div class="row">
    <span class="label">Password:</span>
    <span class="formw"><input type="password" id="password" name="password" size="15" maxlength="15" /></span><br />
    </div>

    <div class="row">
    <span class="label">Password (again):</span>
    <span class="formw"><input type="password" id="password2" name="password2" size="15" maxlength="15" /></span><br />
    </div>

    <div class="row">
    <input type="button" id="createUser" name="createUser" value="Create User" onclick="validateAll()" />
    <input id="reset" name="rest" type="reset" />
    </div>

    </div>
    </form>
    </div>
      <?php include 'footer.inc.php' ?>
    </div>
  </div>
</body>
</html>
