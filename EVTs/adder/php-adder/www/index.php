<?php
session_start();

set_include_path(get_include_path() . PATH_SEPARATOR . '/usr/share/php-adder/');
require_once 'adder_interface.php';

$server = new AdderInterface();
$errors = array();
$err_count = 0;

$valid_authority = isset($_SESSION['is_authority']) ? $_SESSION['is_authority'] : false;

$server->connect('ssl://127.0.0.1');

if (isset($_GET['makeuser']) && $_GET['makeuser'] == 1) {
    show_makeuser_page($errors);
    exit();
} elseif (isset($_POST['createUserSubmitted']) && isset($_POST['user'])
          && isset($_POST['password'])) {
    $result = $server->make_user($_POST['user'], $_POST['password']);
    $server->disconnect();

    if (!$result) {
        $errors[$err_count++] = 'Failed to create user ' . $_POST['user'];
    }

    show_makeuser_success_page($_POST['user'], $errors);
    exit();
} elseif (isset($_GET['action']) && $_GET['action'] == 'logout') {
    unset($_SESSION['session_id']);
    unset($_SESSION['user_id']);
    unset($_SESSION['is_authority']);
    $server->disconnect();
    header('Location: procadmin.php');
    exit();
} elseif (isset($_POST['procedure'])) {
    $procedure = $_POST['procedure'];
} elseif (isset($_GET['procedure'])) {
    $procedure = $_GET['procedure'];
    $stage = $server->get_stage($procedure);
}

$valid_user = false;
$valid_authority = false;
$user = isset($_SESSION['user_id']) ? $_SESSION['user_id'] : null;

if (isset($_SESSION['user_id']) && isset($_SESSION['password'])
    && isset($procedure) && isset($_SESSION['session_id'])) {
    $valid_user = $server->login($_SESSION['user_id'], $_SESSION['password'], $procedure, $is_authority, $_SESSION['session_id']);
}

if (isset($_POST['loginSubmitted']) && isset($_POST['user']) && isset($_POST['password'])) {
    $valid_user = $server->login($_POST['user'], $_POST['password'], $procedure, $is_authority, $_SESSION['session_id']);

    if ($valid_user) {
        $_SESSION['session_id'] = time() + ADDER_SESSION_TIME_LIMIT;
        $_SESSION['user_id'] = $_POST['user'];
        $_SESSION['password'] = $_POST['password'];
        $_SESSION['is_authority'] = $is_authority;
    } else {
        $errors[$err_count++] = $server->get_error();
    }
} elseif (!isset($_SESSION['user_id']) && isset($_GET['procedure']) && isset($_GET['action']) && $_GET['action'] == 'login') {
    $procedure = $_GET['procedure'];
    show_login_page($user, $procedure, 1, $errors);
    $server->disconnect();
    exit();
} elseif (isset($_SESSION['session_id']) && isset($procedure) 
          && isset($_SESSION['user_id'])) {
    $valid_user = $server->verify_session($_SESSION['session_id'], $procedure, $_SESSION['user_id'], $is_authority);
    $_SESSION['is_authority'] = ($valid_user && $is_authority);
}

$valid_authority = isset($_SESSION['is_authority']) ? $_SESSION['is_authority'] : false;

if (isset($_POST['pubkeySubmitted'])) {
    $pubkey = $_POST['authPubKey'];
    $key_constants = $server->get_key_constants($procedure);
    $stage = $server->get_stage($procedure);

    if ($stage != ADDER_STAGE_WAITKEYS) {
        $errors[$err_count++] = 'You are not allowed to submit a public key at this time.';
        show_key_creation_page($user, $procedure, $key_constants, $_POST['pubkeySubmitted'] + 1, $errors);
    } elseif (!$valid_authority) {
        $errors[$err_count++] = 'You are not authorized to submit a public key, or you have not logged in.';
        show_key_creation_page($_SESSION['user_id'], $procedure, $key_constants, $_POST['pubkeySubmitted'] + 1, $errors);
    } else {
        if (!$server->submit_public_key($pubkey, $procedure)) {
            $errors[$err_count++] = $server->get_error();
            show_key_creation_page($_SESSION['user_id'], $procedure, $key_constants, $_POST['pubkeySubmitted'] + 1, $errors);
        } else {
            show_pubkey_success_page($_SESSION['user_id'], $procedure);
        }
    }

    $server->disconnect();
    exit();
} elseif (isset($_POST['polynomialSubmitted'])) {
    $polynomial = $_POST['authPolynomial'];
    $gvalues = $_POST['gValues'];
    $threshold = $server->get_threshold($procedure);
    $key_list = $server->get_auth_pubkeys($procedure);
    $stage = $server->get_stage($procedure);    

    if ($stage != ADDER_STAGE_WAITPOLYNOMIAL) {
        $errors[$err_count++] = 'You are not allowed to submit secret share information at this time.';
        show_polynomial_creation_page($user, $procedure, $key_list, $threshold, $_POST['polynomialSubmitted'] + 1, $errors);
    } elseif (!$valid_authority) {
        $errors[$err_count++] = 'You are not authorized to submit secret share information, or you have not logged in.';
        show_polynomial_creation_page($user, $procedure, $key_list, $threshold, $_POST['polynomialSubmitted'] + 1, $errors);
    } else {
        if (!$server->submit_polynomial($polynomial, $gvalues, $procedure)) {
            $errors[$err_count++] = $server->get_error();
            show_polynomial_creation_page($user, $procedure, $key_list, $threshold, $_POST['polynomialSubmitted'] + 1, $errors);
        } else {
            show_polynomial_success_page($user, $procedure);
        }
    }

    $server->disconnect();
    exit();
} elseif (isset($_POST['privateKeySaved'])) {
    show_privatekey_success_page($user, $procedure);
    $server->disconnect();
    exit();
} elseif (isset($_POST['voteSubmitted'])) {
    $vote = $_POST['encryptedVote'];
    $vote_array = explode(':', $vote);
    $pubkey = $_POST['serverPublicKey'];

    if (isset($stage) && $stage != ADDER_STAGE_VOTING) {
        $errors[$err_count++] = 'You are not allowed to vote at this time.';
        show_vote_submission_page($user, $procedure, $pubkey, $_POST['voteSubmitted'] + 1, $errors);
    } elseif (isset($valid_user) && !$valid_user) {
        $errors[$err_count++] = 'You are not authorized to vote, or you have not logged in.';
        show_vote_submission_page($user, $procedure, $pubkey, $_POST['voteSubmitted'] + 1, $errors);
    } else {
        if (isset($vote_array) && is_array($vote_array) && isset($pubkey) && isset($_POST['voteSubmitted'])
            && !$server->submit_choice($vote_array[0], $vote_array[1], $procedure)) {
            $errors[$err_count++] = $server->get_error();
            show_vote_submission_page($user, $procedure, $pubkey, $_POST['voteSubmitted'] + 1, $errors);
        } else {
            $short_hash = $server->get_short_hash($procedure, $user);
            show_vote_success_page($user, $procedure, $short_hash);
        }
    }

    $server->disconnect();
    exit();
} elseif (isset($_POST['decryptionSubmitted']) && isset($_POST['partialDecryption'])) {
    $cipher_sum = $server->get_cipher_sum($procedure);
    $num_votes = $server->get_num_votes($procedure);
    $decrypted_sum = $_POST['partialDecryption'];
    $stage = $server->get_stage($procedure);

    if ($stage != ADDER_STAGE_WAITDECRYPT) {
        $errors[$err_count++] = 'You are not allowed to submit decryptions at this time.';
        show_decryption_page($user, $procedure, $cipher_sum, $num_votes, $_POST['decryptionSubmitted'] + 1, $errors);
    } elseif (!$valid_authority) {
        $errors[$err_count++] = 'You are not authorized to submit decryptions, or you have not logged in.';
        show_decryption_page($user, $procedure, $cipher_sum, $num_votes, $_POST['decryptionSubmitted'] + 1, $errors);
    } else {
        if (!$server->submit_decrypted_sum($decrypted_sum, $procedure)) {
            $errors[$err_count++] = $server->get_error();
            show_decryption_page($user, $procedure, $cipher_sum, $num_votes, $_POST['decryptionSubmitted'] + 1, $errors);
        } else {
            show_decryption_success_page($user, $procedure);
        }
    }

    $server->disconnect();
    exit();
}

if ($valid_authority && isset($stage) && $stage == ADDER_STAGE_WAITKEYS) {
    $key_constants = $server->get_key_constants($procedure);
    show_key_creation_page($user, $procedure, $key_constants, 1, $errors);
    $server->disconnect();
    exit();
} elseif ($valid_authority && isset($stage) && $stage == ADDER_STAGE_WAITPOLYNOMIAL) {
    $threshold = $server->get_threshold($procedure);
    $key_list = $server->get_auth_pubkeys($procedure);
    show_polynomial_creation_page($user, $procedure, $key_list, $threshold, 1, $errors);
    $server->disconnect();
    exit();
} elseif ($valid_authority && isset($stage) && $stage == ADDER_STAGE_WAITGETPRIVKEYS) {
    $privkey_components = $server->get_privkey_components($procedure);
    show_save_privkey_page($user, $procedure, $privkey_components, 1, $errors);
    $server->disconnect();
    exit();
} elseif ($valid_authority && isset($stage) && $stage == ADDER_STAGE_WAITDECRYPT) {
    $cipher_sum = $server->get_cipher_sum($procedure);
    $num_votes = $server->get_num_votes($procedure);
    show_decryption_page($user, $procedure, $cipher_sum, $num_votes, 1, $errors);
    $server->disconnect();
    exit();
} elseif ($valid_user && isset($stage) && $stage == ADDER_STAGE_VOTING) {
    $pubkey = $server->get_public_key($procedure);
    show_vote_submission_page($user, $procedure, $pubkey, 1, $errors);
    $server->disconnect();
    exit();
} elseif (isset($stage) && isset($stage) && $stage == ADDER_STAGE_INVALID) {
    $errors[$err_count++] = $server->get_error();
} elseif (!isset($_GET['action'])) {
    $procedures = $server->get_procedure_list();
    show_proc_register_list_page($procedures, 1, false);
    $server->disconnect();
    exit();
}

$server->disconnect();

// if (isset($user) && isset($procedure) && isset($_GET['login'])) {
//     show_login_page($user, $procedure, 1, $errors);
// } else {
//     $procedures = $server->get_procedure_list();
//     show_proc_register_list_page($procedures, 1, false);
//     $server->disconnect();
//     exit();
// }

/**
 * Display the procedure registration list page.
 * @param $procedures the list of procedure ids
 */
function show_proc_register_list_page($procedures)
{
    include 'procregisterlist.inc.php';
}

exit();

/**
 * Display the user creation page.
 *
 * @param $errors any errors encountered
 */
function show_makeuser_page($errors)
{
    require_once 'makeuser.inc.php';
}

/**
 * Display the user creation success page.
 *
 * @param $user the user created
 * @param $errors any errors encountered
 */
function show_makeuser_success_page($user, $errors)
{
    require_once 'makeusersuccess.inc.php';
}

/**
 * Displays the form for authority decryption of sum.
 * @param $cipher_sum the encrypted sum
 * @param $num_votes the nubmer of valid votes
 * @param $submit_count the number of times the form has been submitted
 * @param $errors an array of errors that have occured or @b false if no errors
 * have occurred
 */
function show_decryption_page($user, $procedure, $cipher_sum, $num_votes, $submit_count, $errors)
{
    require_once 'decrypt.inc.php';
}

/**
 * Display the page denoting successful submission of a decryption.
 */
function show_decryption_success_page($user, $procedure)
{
    require_once 'decryptsuccess.inc.php';
}

/**
 * Displays the form for authority public key creation.
 * @param $key_constants the key constants for the procedure
 * @param $submit_count the number of times the form has been submitted
 * @param $errors an array of errors that have occured or @b false if no errors
 * have occurred
 */
function show_key_creation_page($user, $procedure, $key_constants, $submit_count, $errors)
{
    require_once 'createkey.inc.php';
}

/**
 * Displays the form for user and authority login.
 * @param $submit_count the number of times the user has (unsuccessfully) tried to log in.
 * @param $errors an array of error descriptions or @b false if there were no errors.
 */
function show_login_page($user, $procedure, $submit_count, $errors)
{
    require_once 'login.inc.php';
}

/**
 * Display the page denoting successful logout.
 */
function show_logout_success_page($user, $procedure)
{
    require_once 'logoutsuccess.inc.php';
}

/**
 * Displays the form for authority polynomial generation and submission.
 * @param $key_str the appropriate portions of all the authorities' keys
 * @param $threshold the threshold of authorities for this procedure
 * @param $submit_count the number of times the form has been submitted
 * @param $errors an array of errors that have occured or @b false if no errors
 * have occurred
 */
function show_polynomial_creation_page($user, $procedure, $key_str, $threshold, $submit_count, $errors)
{
    require_once 'createpolynomial.inc.php';
}

/**
 * Display the page denoting successful submission of a polynomial.
 */
function show_polynomial_success_page($user, $procedure)
{
    require_once 'polynomialsuccess.inc.php';
}

/**
 * Display the page denoting successful submission of a private key.
 */
function show_privatekey_success_page($user, $procedure)
{
    require_once 'saveprivatekeysuccess.inc.php';
}

/**
 * (No longer used.)
 * @param $privkey the private key
 * @param $submit_count the number of times the form has been submitted
 * @param $errors an array of errors that have occured or @b false if no errors
 * have occurred
 */
function show_privkey_page($user, $procedure, $privkey, $submit_count, $errors)
{
    require_once 'getprivkey.inc.php';
}

/**
 * Displays the list of procedures for selection.
 * @param $procedures the list of active procedures
 * @param $submit_count the number of times the form has been submitted
 * @param $errors an array of errors that have occured or @b false if no errors
 * have occurred
 */
function show_procedure_selection_page($procedures, $submit_count, $errors)
{
    require_once 'selectproc.inc.php';
}

/**
 * Display the page denoting successful submission of a public key.
*/
function show_pubkey_success_page($user, $procedure)
{
    require_once 'pubkeysuccess.inc.php';
}

/**
 * Displays the form for saving the authority's private key.
 * @param $private_key_components the private key components
 * @param $submit_count the number of times the form has been submitted
 * @param $errors an array of errors that have occured or @b false if no errors
 * have occurred
 */
function show_save_privkey_page($user, $procedure, $private_key_components, $submit_count, $errors)
{
    require_once 'saveprivatekey.inc.php';
}

/**
 * Displays the form for choice (vote) submission.
 * @param $pubkey the public key for this procedure
 * @param $submit_count the number of times the form has been submitted
 * @param $errors an array of errors that have occured or @b false if no errors
 * have occurred
 */
function show_vote_submission_page($user, $procedure, $pubkey, $submit_count, $errors)
{
    require_once 'vote.inc.php';
}

/**
 * Display the page denoting successful submission of a choice (vote).
*/
function show_vote_success_page($user, $procedure, $short_hash)
{
    require_once 'votesuccess.inc.php';
}
?>
