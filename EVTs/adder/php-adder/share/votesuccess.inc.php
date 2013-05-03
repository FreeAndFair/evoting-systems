<?php require_once 'header.inc.php' ?>
</head>
<body>
  <div class="container">
    <?php include 'sidebar.inc.php' ?>

    <div class="mainContent">
      <h1>Vote Submitted</h1>

      <p>Your vote has been recorded. Thank you for
      participating.</p>

      <p>When the procedure is finished, the results
      may be viewed by selecting &quot;Procedures&quot;, and clicking on the
      status link next to the procedure name.</p>

      <p>To provide some assurance of the integrity of your vote,
      your vote has a security code associated with it. At any
      time, you can compare the code to the code stored with your
      vote on the status page.</p>

      <?php if (isset($short_hash) && is_string($short_hash) && strlen($short_hash) > 0) { ?>
      <p>Your code is:
      <strong><?php echo $short_hash; ?></strong>.</p>
      <?php } ?>
      <?php include 'footer.inc.php' ?>
    </div>
  </div>
</body>
</html>
