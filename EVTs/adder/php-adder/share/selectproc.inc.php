<?php require_once 'header.inc.php' ?>
</head>

<body>
  <div class="container">
    <?php include 'sidebar.inc.php' ?>

    <div class="mainContent">
      <h1><span style="font-variant: small-caps">Adder</span>: A Secure Online Voting
      System</h1>

      <p>Welcome to the <span style="font-variant: small-caps">Adder</span> secure online
      voting system. Please read <a href="guide.php">The Beginner's
      Guide to <span style="font-variant: small-caps">Adder</span></a> if you would like
      an overview of the system, or visit the <span style=
      "font-variant: small-caps">Adder</span> <a href=
      "http://www.cse.uconn.edu/~adder/">Web site</a>.</p>

      <p>Below you will find a list of currently running
      procedures. To see more information about the active
      procedures, select the &quot;Procedures&quot; option from the menu.</p>

      <h2>Active Procedures</h2>
      <?php
      function cmp($a, $b)
      {
         $a = $a['title'];
         $b = $b['title'];
         return strcasecmp($a, $b);
      }

      $active_procs = 0;
      $num_procs = count($procedures);

      if ($num_procs > 0) {
          echo "<ul>\n";

          usort($procedures, "cmp");

          foreach ($procedures as $procedure) {
              if ($procedure['stage'] != ADDER_STAGE_NOTSTARTED) {
                  $active_procs++;
                  $query_string = "procedure=" . urlencode($procedure['id']) . "&title=" . urlencode($procedure['title']);
                  echo '    <li><a href="status.php?' . htmlentities($query_string) . '">' . $procedure['title'] . "</a></li>\n";
              }
          }

          echo "</ul>\n";
      }

      if ($active_procs == 1) {
          echo "<p>There is <strong>" . $active_procs . "</strong> active procedure.</p>";
      } elseif ($num_procs > 1) {
          echo "<p>There are <strong>" . $active_procs . "</strong> active procedures.</p>";
      }

      ?>
      <?php require_once 'footer.inc.php' ?>
    </div>
  </div>
</body>
</html>
