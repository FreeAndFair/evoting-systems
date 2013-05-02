<?php
error_reporting(E_ALL | E_STRICT);
session_start();
set_include_path(get_include_path() . PATH_SEPARATOR . '/usr/share/php-adder/');
require_once 'adder_interface.php';

$server = new AdderInterface();
$server->connect(DEFAULT_SERVER);

/**
 * Make sure to return a valid time, or else 0.
 *
 * @param $str the time string
 * @param $sub the amount of time to substract (i.e., time())
 * @return the duration
 */
function makevalidtime($str, $now) {
    if (is_null($str)) {
        return 0;
    }

    $time = strtotime($str);

    if ($time === false || $time == -1) {
        return 0;
    }

    $duration = $time - $now;

    if ($duration < 0) {
        return 0;
    }

    return $duration;
}

if (isset($_POST['createSubmitted'])) {
    if (isset($_POST['title']) && isset($_POST['text']) && 
        isset($_POST['threshold']) && isset($_POST['publickeytime']) &&
        isset($_POST['polynomialtime']) &&
        isset($_POST['secretkeytime']) && isset($_POST['votetime']) &&
        isset($_POST['keylength']) && isset($_POST['robustness']) &&
        isset($_POST['min']) && isset($_POST['max']) && 
        isset($_POST['choices']) && isset($_POST['authorities'])) {
        $now = time();
        $publickeytime = makevalidtime($_POST['publickeytime'], $now);
        $polynomialtime = makevalidtime($_POST['polynomialtime'], $now);
        $secretkeytime = makevalidtime($_POST['secretkeytime'],  $now);
        $votetime = makevalidtime($_POST['votetime'], $now);

        $server->create_procedure($_POST['title'],
                                  $_POST['text'], 
                                  $_POST['threshold'],
                                  $publickeytime,
                                  $polynomialtime,
                                  $secretkeytime,
                                  $votetime, 
                                  $_POST['keylength'],
                                  $_POST['robustness'],
                                  $_POST['min'],
                                  $_POST['max'],
                                  $_POST['choices'],
                                  $_POST['authorities']);
    } else {
        $users = $server->get_user_list();
        show_create_procedure($users);
        $server->disconnect();
        exit();
    }
} else {
    if (isset($_GET['start'])) {
        $server->start_procedure($_GET['start']);
    } elseif (isset($_GET['stop'])) {
        $server->stop_procedure($_GET['stop']);
    } elseif (isset($_GET['create'])) {
        $users = $server->get_user_list();
        show_create_procedure($users);
        $server->disconnect();
        exit();
    } elseif (isset($_GET['delete'])) {
        $server->delete_procedure($_GET['delete']);
    } elseif (isset($_GET['progress'])) {
        $server->progress_procedure($_GET['progress']);
        $_GET['procedure'] = $_GET['progress'];
    }
}

$procedures = $server->get_procedure_list();
show_proc_register_list_page($procedures, 1, false);
$server->disconnect();
exit();
 
/**
 * Display the procedure registration list page.
 * @param $procedures the list of procedure ids
 */
function show_proc_register_list_page($procedures)
{
    include 'procregisterlist.inc.php';
}

function show_create_procedure($users)
{
    include 'createprocedure.inc.php';
}
