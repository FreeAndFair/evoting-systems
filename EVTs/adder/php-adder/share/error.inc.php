<p id="errorListHeaderText">Errors found:</p>
  <ul id="errorMessageBlock">
<?php
    foreach ($errors as $error_message) {
        echo "    <li>$error_message</li>\n";
    }
?>
  </ul>
      <?php include 'footer.inc.php' ?>
    </div>
  </div>
</body>
</html>

