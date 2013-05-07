<?php require_once 'header.inc.php' ?>
<?php if (ADMIN) {?>
 <script type="text/javascript" src="scripts/procregisterlist.js">
      </script>
      <?php } ?>
</head>

<body>
<div class="container">
<?php include 'sidebar.inc.php' ?>
<div class="mainContent">

<h1>Procedures</h1>

<h2>Available Procedures</h2>
<?php
$server = new AdderInterface();
$server->connect(DEFAULT_SERVER);

function cmp($a, $b)
{
    $a = $a['title'];
    $b = $b['title'];
    return strcasecmp($a, $b);
}

if (isset($procedures) && is_array($procedures) && !empty($procedures)) {

    usort($procedures, "cmp");

    echo '<table summary="Active procedures">' . "\n";

    foreach ($procedures as $procedure) {
        $name = $procedure["title"];
        $length = strlen($name);

        if ($length > 30) {
            $name = substr($name, 0, 30) . "...";
        }

        echo '<tr><td align="left"><strong>' . $name . '</strong>';
 
        $remaining = $server->get_remaining($procedure['id']);

        if ($procedure['stage'] == ADDER_STAGE_NOTSTARTED) {
            echo ' <span style="font-size: small">(<strong>Stage:</strong> Not started)</span>';
        } elseif ($procedure['stage'] == ADDER_STAGE_FINISHED) {
            echo ' <span style="font-size: small">(<strong>Stage:</strong> Finished)</span>';
        } elseif ($procedure['stage'] == ADDER_STAGE_HALTED) {
            echo ' <span style="font-size: small">(<strong>Stage:</strong> Halted)</span>';
        } else {
            echo ' <span style="font-size: small">(<strong>Stage:</strong> ' . $procedure['stage'] . ' <strong>Authorities needed:</strong> ' . $remaining . ')</span>';
        }

        echo '<br /></td>' . "\n";

        $query_string = 'procedure=' . urlencode($procedure['id']) . '&title=' . urlencode($procedure['title']);
        echo '    <td>(<a href="status.php?' . htmlentities($query_string) . '">Status</a>)</td>' . "\n";
        
        if (VOTER && $procedure["stage"] == ADDER_STAGE_VOTING) {
            if (isset($_SESSION['user_id'])) {
                $query_string = 'user=' . urlencode($_SESSION['user_id']) . '&procedure=' . urlencode($procedure["id"]) . '&action=login';
                echo '    <td>(<a href="index.php?' . htmlentities($query_string) . '">Participate</a>)</td>' . "\n";
            } else {
                $query_string = 'procedure=' . urlencode($procedure['id']) . '&action=login';
                echo '    <td>(<a href="index.php?' . htmlentities($query_string) . '">Login</a>)</td>' . "\n";
            }
        }
        
        echo '</tr>' . "\n";

    } // end foreach
    echo '</table>' . "\n";
}

$server->disconnect();

if (count($procedures) == 0) {
    echo '<p>There are no registered procedures.</p>';
}

?>
<?php include 'footer.inc.php' ?>
</div>
</div>
</body>
</html>
