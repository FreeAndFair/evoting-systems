<?php require_once 'header.inc.php' ?>
</head>
<body>

  <div class="container">
    <?php include 'sidebar.inc.php' ?>

    <div class="mainContent">
      <h1>User Creation</h1>
<?php
if (isset($errors) && is_array($errors) && count($errors) > 0) {
    require_once 'error.inc.php';
    exit();
}
?>
    <p>Your new user account <strong><?php echo $user; ?></strong> has been created. You may now
    <a href="procadmin.php">login</a>.</p>
</div>
</div>

</body>

</html>
