<?php
error_reporting(E_ALL | E_STRICT);
session_start();
set_include_path(get_include_path() . PATH_SEPARATOR . '/usr/share/php-adder/');
require_once 'adder_interface.php';

$server = new AdderInterface();

if (isset($_GET['procedure'])) {
    $procedure = $_GET['procedure'];

    if (isset($_GET['auth_id'])) {
        $auth_id = $_GET['auth_id'];
        $key = '';

        if (!empty($auth_id)) {
           $server->connect(DEFAULT_SERVER);
           $key = $server->get_auth_pub_key($procedure, $auth_id);
           $server->disconnect();
        }

        show_authority_key($auth_id, $key);
        exit();
    } elseif (isset($_GET['user_id'])) {
        $voter = $_GET['user_id'];
        $server->connect(DEFAULT_SERVER);
        $vote = $server->get_vote($procedure, $voter);
        $short_hash = $server->get_short_hash($procedure, $voter);
        $server->disconnect();
        show_vote($voter, $vote, $short_hash);
        exit();
    } elseif (isset($_GET['ballot_proof'])) {
        $bp = isset($_GET['ballot_proof']) ? $_GET['ballot_proof'] : '';
        $server->connect(DEFAULT_SERVER);
        $ballot_proof = $server->get_ballot_proof($procedure, $bp);
        $server->disconnect();
        show_ballot_proof($bp, $ballot_proof);
        exit();
    } else {
        $server->connect(DEFAULT_SERVER);
        $votes = $server->get_vote_list($procedure);
        $candidates = $server->get_choices($procedure);
        $question = $server->get_description($procedure);
        $pubkeys = $server->get_pubkey_list($procedure);
        $stage = $server->get_stage($procedure);
        $times = $server->get_times($procedure);
        $procedures = $server->get_procedure_list();
        $min = $procedures[$procedure]['min'];
        $max = $procedures[$procedure]['max'];
        $server->disconnect();
        show_status($stage, $pubkeys, $votes, $candidates, $question, $times, $min, $max);
        exit();
    }
} else {
    $server->connect(DEFAULT_SERVER);
    $procedures = $server->get_procedure_list();
    $server->disconnect();
    show_server_status_page($procedures, 1, false);
    exit();
}

function crc24($str)
{
    define('CRC24_INIT', 0xb704ce);
    define('CRC24_POLY', 0x1864cfb);

    $crc = CRC24_INIT;
    $x = 0;

    $len = strlen($str);

    while ($len--) {
        $crc ^= ord($str[$x++]) << 16;

        for ($i = 0; $i < 8; $i++) {
            $crc <<= 1;

            if ($crc & 0x1000000) {
                $crc ^= CRC24_POLY;
            }
        }
    }

    return $crc & 0xffffff;
}

/**
 * Display the data of the given string with the given header.
 *
 * @param $str the string
 * @param $head the object header
 * @return the data
 */
function display_data($str, $head)
{
    $crc = crc24($str);
    $crc = pack('CCC', ($crc >> 8) & 0xff, ($crc >> 4) & 0xff, ($crc >> 0) & 0xff);
    $crc = base64_encode($crc);
    $tmp = bzcompress($str);
    $tmp = base64_encode($tmp);
    $tmp = chunk_split($tmp);
    $out = '-----BEGIN ' . $head . "-----\nVersion: 0.0.1\nCompression: bzip2\n";

    if (!strcmp($head, 'ADDER PUBLIC KEY')) {
        $out .= "Cipher: Elgamal\n";
        $out .= 'Comment: "1024-bit Elgamal"';
        $out .= "\n";
    }

    $out .= "\n" . $tmp . '=' . $crc . "\n-----END " . $head . "-----\n";

    return $out;
}

/**
 * Convert a duration in seconds to an array representing the time remaining.
 *
 * @param $duration the duration in seconds
 * @return the array
 */
function get_duration($duration) {
    define('SEC_YEAR', 365 * 24 * 60 * 60);
    define('SEC_MONTH', 30 * 24 * 60 * 60);
    define('SEC_WEEK', 7 * 24 * 60 * 60);
    define('SEC_DAY', 24 * 60 * 60);
    define('SEC_HOUR', 60 * 60);
    define('SEC_MINUTE', 60);

    $output = array();

    if ($duration >= SEC_YEAR) {
        $output['year'] = floor($duration / SEC_YEAR);
        $duration -= $output['year'] * SEC_YEAR;
    }

    if ($duration >= SEC_MONTH) {
        $output['month'] = floor($duration / SEC_MONTH);
        $duration -= $output['month'] * SEC_MONTH;
    }

    if ($duration >= SEC_WEEK) {
        $output['week'] = floor($duration / SEC_WEEK);
        $duration -= $output['week'] * SEC_WEEK;
    }

    if ($duration >= SEC_DAY) {
        $output['day'] = floor($duration / SEC_DAY);
        $duration -= $output['day'] * SEC_DAY;
    }

    if ($duration >= SEC_HOUR) {
        $output['hour'] = floor($duration / SEC_HOUR);
        $duration -= $output['hour'] * SEC_HOUR;
    }

    if ($duration >= SEC_MINUTE) {
        $output['minute'] = floor($duration / SEC_MINUTE);
        $duration -= $output['minute'] * SEC_MINUTE;
    }

    if ($duration >= 0) {
        $output['second'] = $duration;
    }

    return $output;
}

/**
 * Convert a duration in seconds to an English string representing the time
 * remaining.
 *
 * @param $duration the duration in seconds
 * @return the English string
 */
function get_time_left($duration)
{
    $a = get_duration($duration);
    $time_left = '';
    $keys = array_keys($a);

    foreach ($keys as $key) {
        $time_left .= $a[$key] . ' ' . $key;

        if ($a[$key] > 1) {
            $time_left .= 's ';
        } else {
            $time_left .= ' ';
        }
   }

   return trim($time_left);
}

function get_deadline($stage, $times)
{
    if (!isset($times) || !is_array($times) || count($times) != 5) {
        return 'Unable to retrieve deadline.';
    }

    $time = 0;

    if (isset($times[0])) {
        $time = $times[0];
    }

    /**
     * times:
     *
     * 0: create_time
     * 1: public_key_time
     * 2: polynomial_time
     * 3: secret_key_time
     * 4: vote_time
     */
    switch ($stage) {
    case ADDER_STAGE_VOTING:
        $time += $times[4];
    case ADDER_STAGE_WAITGETPRIVKEYS:
        $time += $times[3];
    case ADDER_STAGE_WAITPOLYNOMIAL:
        $time += $times[2];
    case ADDER_STAGE_WAITKEYS:
        $time += $times[1];
        break;
    default:
        $time = -1;
    }

    if ($time >= 0) {
        date_default_timezone_set('US/Eastern');
        $date = strftime('%A %B %e, %Y %I:%M:%S %p %Z', $time);
        $now = time();
        $remaining = $time - $now;
        $date_now = strftime('%A %B %e, %Y %I:%M:%S %p %Z', $now);

        if ($remaining < 0) {
            $remaining = 0;
        }

        $date = $date . '<br /><br /><strong>Time left:</strong> ' . get_time_left($remaining) . ' remaining as of ' . $date_now;
    } else {
        $date = 'No deadline for this stage.';
    }

    return $date;
}

/**
 * Display the status of a procedure, including a text description of the stage.
 *
 * @param $stage the stage of the procedure
 * @param $pubkeys the user ids of authorities who have submitted public keys
 * @param $votes the user ids of users who have submitted votes
 * @param $candidates the candidates
 * @param $question the ballot question
 * @param $times the times
 * @param $min the minimum choices
 * @param $max the maximum choices
 */
function show_status($stage, $pubkeys, $votes, $candidates, $question, $times, $min, $max)
{
    $deadline = get_deadline($stage, $times);

    $stage_descr = 'The server is currently offline';

    switch ($stage) {
    case ADDER_STAGE_NOTSTARTED:
        $stage_descr = 'This procedure has not yet started';
        break;
    case ADDER_STAGE_WAITKEYS:
        $stage_descr = 'The server is currently waiting for authorities to submit their public keys';
        break;
    case ADDER_STAGE_WAITPOLYNOMIAL:
        $stage_descr = 'The server is currently waiting for authorities to submit their secret share information';
        break;
    case ADDER_STAGE_WAITGETPRIVKEYS:
        $stage_descr = 'The server is currently waiting for authorities to create their private keys';
        break;
    case ADDER_STAGE_COMPUTINGPUBKEY:
        $stage_descr = 'The server is currently performing the final computations to initiate the procedure.';
        break;
    case ADDER_STAGE_VOTING:
        $stage_descr = 'The server is currently accepting votes';
        break;
    case ADDER_STAGE_ADDCIPHER:
        $stage_descr = 'The server is currently counting votes';
        break;
    case ADDER_STAGE_WAITDECRYPT:
        $stage_descr = 'The server is currently waiting for authorities to decrypt the sum';
        break;
    case ADDER_STAGE_DECRYPTING:
        $stage_descr = 'The server is currently calculating the final result';
        break;
    case ADDER_STAGE_FINISHED:
        $stage_descr = 'The procedure has finished';
        break;
    case ADDER_STAGE_HALTED:
        $stage_descr = 'The server is currently halted since not enough authorities have participated';
        break;
    case ADDER_STAGE_NONEXIST:
        $stage_descr = 'The procedure does not exist';
        break;
    default:
        $stage_descr = 'Invalid'; 
    }

    include 'procedurestatus.inc.php';
}

/**
 * Display the server status page.
 *
 * @param $procedures the list of procedure ids
 */
function show_server_status_page($procedures)
{
    include 'serverstatus.inc.php';
}

/**
 * Display a user's vote.
 *
 * @param $vote the vote
 */
function show_vote($voter, $vote, $short_hash)
{
    include 'getvote.inc.php';
}

/**
 * Display a user's ballot proof.
 *
 * @param $ballot_proof the proof
 */
function show_ballot_proof($bp, $ballot_proof)
{
    include 'getballotproof.inc.php';
}

/**
 * Display an authority's public key.
 *
 * @param $pubkey the public key
 */
function show_authority_key($auth_id, $pubkey)
{
    include 'getauthkey.inc.php';
}
