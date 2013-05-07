<?php
    set_include_path(get_include_path() . PATH_SEPARATOR . '../share');
    require_once 'adder_interface.php';
    require_once 'header.inc.php';
?>
</head>

<body>
  <div class="container">
    <?php include 'sidebar.inc.php'; ?>

    <div class="mainContent">
      <h1>The Beginner&apos;s Guide to <span style=
      "font-variant: small-caps">Adder</span></h1>

      <h2>A Brief System Overview</h2>

      <p><span style="font-variant: small-caps">Adder</span> is a Web-based voting system
      which requires no additional hardware and can run on various
      platforms (including Windows, Linux, and others).</p>

      <p>An <span style="font-variant: small-caps">Adder</span> election procedure is
      initiated through a Web-based interface which allows the
      administrator to provide the list of choices and specify the
      eligible users. Such users are <em>voters</em> and
      <em>authorities</em> and are selected from a database that is
      available to the server.</p>

      <p>An <span style="font-variant: small-caps">Adder</span> election procedure
      progresses in the following manner:</p>

      <ol>
        <li>The authorities log onto the system via a Web browser
        and participate in a protocol that results in the creation
        of a public encryption key for the system, and a unique
        private decryption key for each authority.</li>

        <li>Next, each voter logs on, downloads the public key of
        the system, and uses that to encrypt a vote, which is
        placed in an area of public storage specifically reserved
        for that voter.</li>

        <li>When the election procedure is over, the server totals
        the votes (using special encryption properties) and posts
        the encrypted result.</li>

        <li>The authorities then partially decrypt the encrypted
        result with their private keys.</li>

        <li>When enough partial decryptions have been collected,
        the server combines them to form the election procedure
        result, which is published.</li>
      </ol>

      <p>We note that <span style="font-variant: small-caps">Adder</span> does not employ
      any user-to-user communication; instead, users communicate
      indirectly through the &quot;main server database&quot; that is
      maintained by the system.</p>

      <p>Please visit our <a href=
      "http://www.cse.uconn.edu/~adder/">Web site</a> for more
      information.</p>

      <h2>Participating</h2>

      <p>If you are a registered user of an <span style=
      "font-variant: small-caps">Adder</span> installation, you can participate as a
      <strong>voter</strong><?php if (AUTHORITY) { ?> or an
      <strong>authority</strong> <?php } ?>.</p><?php
      if (AUTHORITY) {
      ?>

      <p>If you are an <strong>authority</strong>, you can
      participate by logging in at the start of an election
      procedure, and following the instructions shown to you. You
      will need to complete three separate steps before the voting
      begins. Be sure to keep your eye on the status page of the
      procedure to see when each new phase occurs. Once the
      election procedure is over, you may be required to contribute
      a piece of the decryption of the result, so you will need to
      login again and follow the instructions given to
      you.</p><?php
      }
      ?>

      <p>If you are a <strong>voter</strong>, you only need to
      login when the voting phase has begun. You can then select
      your choice and submit it.</p>

      <p>Anyone can view the final election procedure results when
      they have been posted. These can be found on the procedure
      status page.</p><?php
      if (ADMIN) {
      ?>

      <h2>Running Your Own Procedure</h2>

      <p>If you would like to create your own <span style=
      "font-variant: small-caps">Adder</span> procedure, you can do so by selecting
      &quot;Procedures&quot;, and then &quot;Create New Procedure&quot;. You must fill
      out the form that is given to you, and submit it. Once this
      is done, the procedure will be stored on the system.</p>

      <p>You can start the procedure by clicking on the &quot;Start&quot;
      link. This will launch the procedure into the first phase of
      the authority key-creation protocol. The server will enter
      the next phase when the time limit has been reached (which
      you set in the procedure creation page), or until you click
      the &quot;Advance Stage&quot; link. Be aware that you should wait until
      all authorities have had ample opportunity to participate
      before manually advancing the stage.</p>

      <p>If you would like to stop the procedure, you may click on
      the stop link, which will force an end to the current stage.
      If you stop a procedure and then restart it, all information
      will be lost, and the server will start from stage one.</p>

      <p>You may delete a procedure by clicking on &quot;Delete&quot;. Once a
      procedure has been deleted, it cannot be restored.</p><?php
      }
      ?><?php include 'footer.inc.php' ?>
    </div>
  </div>
</body>
</html>
