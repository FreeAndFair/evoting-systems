<?php
error_reporting(E_ALL | E_STRICT);
set_include_path(get_include_path() . PATH_SEPARATOR . '../share');
require_once 'adder_interface.php';
?>

<div class="sidebar">
<a href="index.php">Procedures</a><br />

<?php
if (isset($_SESSION['user_id'])) {
    $query_string = "action=logout";
    echo '  <a href="index.php?' . htmlentities($query_string)
    . '">Log out (<strong>' . $_SESSION['user_id'] . '</strong>)</a>' . "\n";
} ?>
</div>
