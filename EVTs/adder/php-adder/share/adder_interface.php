<?php
/*
 * Adder Interface
 * Copyright (C) 2004, 2005, 2006 The Adder Team <adder@cse.uconn.edu>
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *
 */

error_reporting(E_ALL | E_STRICT);

/**
 * Base Adder interface page.
 *
 * @package Adder
 * @author Eric Dutko
 * @author Michael Korman
 * @author David Walluck
 * @since 0.0.1
 * @version $Id$
 */
define('MAX_PROCEDURES', 100);
define('MAX_USERS', 1000);
define('MAX_VOTERS', 1000);
define('MAX_AUTHORITIES', 100);
define('MAX_CHOICES', 100);

define('ADMIN', true);
define('AUTHORITY', true);
define('VOTER', true);
define('APPLET', true);
define('DEFAULT_SERVER', 'ssl://127.0.0.1');

define('ADDER_VERSION_MAJOR', 1);
define('ADDER_VERSION_MINOR', 9);

define('ADDER_DELIM', "\r\n");

define('ADDER_STAGE_INVALID', -1);
define('ADDER_STAGE_NOTSTARTED', 0);
define('ADDER_STAGE_WAITKEYS', 1);
define('ADDER_STAGE_WAITPOLYNOMIAL', 2);
define('ADDER_STAGE_WAITGETPRIVKEYS', 3);
define('ADDER_STAGE_COMPUTINGPUBKEY', 4);
define('ADDER_STAGE_VOTING', 5);
define('ADDER_STAGE_ADDCIPHER', 6);
define('ADDER_STAGE_WAITDECRYPT', 7);
define('ADDER_STAGE_DECRYPTING', 8);
define('ADDER_STAGE_FINISHED', 9);
define('ADDER_STAGE_HALTED', 10);
define('ADDER_STAGE_NONEXIST', 11);

define('ADDER_DEFAULT_PORT', 6999);
define('ADDER_SESSION_TIME_LIMIT', 300); // 5 minutes

/**
 * Base Adder interface class.
 *
 * @package Adder
 * @author Eric Dutko
 * @author Michael Korman
 * @author David Walluck
 * @since 0.0.1
 * @version $Id$
 */
class AdderInterface
{
    /** @private bool True Set to true if this interface is connected to the server. */
    private $connected;
    /** @private string The most-recently-generated error message. */
    private $error;
    /** @private int The socket connection. */
    private $sock;
    /** @private int The cached stage of the selected procedure. */
    private $stage;
    /** @private string The protocol version used by this interface. */
    private $client_version;
    /** @private string The protocol version used by the server. */
    private $server_version;
    private $proc;

    /**
     * Default constructor.
     */
    function AdderInterface()
    {
        $this->connected = false;
        $this->error = false;
        $this->stage = -1;
        $this->client_version = ADDER_VERSION_MAJOR . "." . ADDER_VERSION_MINOR;
        $this->server_version = "UNKNOWN";
    }

    function send_msg($msg)
    {
        fputs($this->sock, $msg);
    }

    /**
     * Connect to the server.
     *
     * @param string $server the address of the server
     * @param int $port the port on which to connecte
     * @return bool true if successful, false otherwise
     */
    function connect($server, $port = ADDER_DEFAULT_PORT)
    {
        if ($this->connected) {
            return true;
        }

	$this->sock = fsockopen($server, $port, $errno, $errstr, 30);

        if (!$this->sock) {
            $this->error = "Error connecting to server: $errstr ($errno)";
            die($this->error);
        }

        // Send the version information to the server.
        fputs($this->sock, "VERSION \"" . $this->client_version . "\"" . ADDER_DELIM);

        // Read the version information from the server's response. If the
        // version does not match, fail.
        //--- NOTE: This should eventuially behave more intelligently with
        //          respect to determining version compatibility.
        $response = strtoupper(fgets($this->sock));
        $tokens = explode(" ", $response);
        $this->server_version = trim($tokens[1]);
        
        /*        if (strcmp($this->server_version, $this->client_version) != 0) {
            fclose($this->sock);
            $this->error = "Error connecting to server: version incompatibility.\n"
                . "Client version: " . $this->client_version . "\n"
                . "Server version: " . $this->server_version;
            return false;
        }*/
        
        $this->connected = true;
        
        return true;
    }

    /**
     * Send data to the server to create a procedure.
     *
     * @param string $title the procedure title
     * @param string $text the displayed description
     * @param int $threshold the threshold of authorities
     * @param int $publickeytime the duration of the public key submission in seconds
     * @param int $polynomialtime the duration of the polynomial submission in seconds
     * @param int $secretkeytime the duration of the secret key submission in seconds
     * @param int $votetime the duration of the election in seconds
     * @param int $keylength the desired length of the keys in bits
     * @param int $robustness the robustness factor
     * @param int $min the minimum allowed choices
     * @param int $max the maximum allowed choices
     * @param string $choices the choices
     * @param array $authorities the authorities
     * @return bool true if successful or false otherwise
     */
    function create_procedure($title, $text, $threshold, $publickeytime,
                              $polynomialtime, $secretkeytime, $votetime,
                              $keylength, $robustness, $min, $max, $choices_str,
                              $authorities)
    {
        // Fail if there is no connection to server.
        if (!$this->connected) {
            $this->error = "Error creating procedure: not connected to server.";
            return false;
        }

        $command = "ADMIN \"password\"";
        fputs($this->sock, $command . "\n");

        $response = trim(fgets($this->sock));

        $command = "CREATEPROCEDURE \"$title\" \"$text\" $threshold $publickeytime "
            . "$polynomialtime $secretkeytime $votetime $keylength $robustness $min $max ";

        $choices_array = explode("\n", $choices_str);
     
        $choices_s = "(";

        foreach ($choices_array as $choice) {
            $choices_s = $choices_s . '"' . trim($choice) . '",';
        }

        $choices_s = rtrim($choices_s, ',') . ')';

        $auth_str = "(";

        foreach ($authorities as $auth) {
            $auth_str = $auth_str . "\"$auth\",";
        }

        $auth_str = rtrim($auth_str, ',') . ')';

        $command = $command . $choices_s . ' ' . $auth_str;

        fputs($this->sock, $command . "\n");

        // Read the server's response, and return the appropriate message.
        $response = trim(fgets($this->sock));

        if ($response == "CREATEPROCEDURE OK") {
            return true;
        } elseif ($response == "CREATEPROCEDURE FAILURE") {
            $this->error = "Error creating procedure: invalid parameter.";
            return false;
        }
    }

    /**
     * Make a user with the given username and password.
     *
     * @param string $username the username
     * @param string $password the password
     * @return bool true if successful or false otherwise
     */
    function make_user($username, $password)
    {
        // Fail if there is no connection to server.
        if (!$this->connected) {
            $this->error = "Error creating user: not connected to server.";
            return false;
        }

        $command = "ADMIN \"password\"";
        fputs($this->sock, $command . "\n");
        $response = trim(fgets($this->sock));

        fputs($this->sock, 'MAKEUSER "' . $username .'" "' . $password . '" "" "" "" ""' . ADDER_DELIM);

        // Read the server's response, and return the appropriate message.
        $response = trim(fgets($this->sock));

        if (!strcmp($response, "MAKEUSER OK")) {
            $this->error = "";
            return true;
        } elseif (!strcmp($response, "MAKEUSER USEREXISTS")) {
            $this->error = "Error creating user: user already exists.";
            return false;
        } else {
            $this->error = "Error creating user: unknown communication error.";
            return false;
        }
    }

    /**
     * Disconnect from the server.
     */
    function disconnect()
    {
        fclose($this->sock);
        $this->connected = false;
        return;
    }

    /**
     * Get an authority's public key from the server.
     *
     * @param string $auth_id the authority's user id
     * @return mixed the authority's public key
     */
    function get_auth_pub_key($procedure, $auth_id)
    {
        if (!$this->connected) {
            $this->error = "Error getting authority public key from server: not connected to server.";
            return false;
        }

        fputs($this->sock, 'GETAUTHPUBKEY "' . $procedure . '" "' . $auth_id . '"' . ADDER_DELIM);
        $response = trim(fgets($this->sock));

        if (!strcmp($response, "GETAUTHPUBKEY BADPROCEDURE")) {
            $this->error = "Error getting authority public key from server: invalid procedure.";
            return false;
        } elseif (!strcmp($response, "GETAUTHPUBKEY BADSTAGE")) {
            $this->error = "Error getting authority public key from server: this is not yet the proper stage to retrieve authority public keys.";
            return false;
        } elseif (!strcmp($response, "GETAUTHPUBKEY NOKEY")) {
            $this->error = "Error getting authority public key from server: authority has not submitted a public key yet.";
            return false;
        } else {
            preg_match('@GETAUTHPUBKEY\s*\"(\w*)\"@', $response, $matches);
            return $matches[1]; // FIXME
        }
    }

    /**
     * Get an authority's stage from the server.
     *
     * @param string $auth_id the authority's user id
     * @return mixed the authority's stage
     */
    function get_auth_stage($procedure, $auth_id)
    {
        if (!$this->connected) {
            $this->error = "Error getting authority stage from server: not connected to server.";
            return false;
        }

        fputs($this->sock, 'GETAUTHSTAGE "' . $procedure . '" "' . $auth_id . '"' . ADDER_DELIM);
        $response = trim(fgets($this->sock));

        if ($response == "GETAUTHSTAGE BADPROCEDURE") {
            $this->error = "Error getting authority stage from server: invalid procedure.";
            return false;
        } elseif ($response == "GETAUTHSTAGE INVALIDAUTHORITY") {
            $this->error = "Error getting authority stage from server: invalid authority.";
            return false;
        } else {
            preg_match('@GETAUTHSTAGE\s*(\d*)@', $response, $matches);
            return $matches[1]; // FIXME
        }
    }

    /**
     * Get the description of a procedure.
     *
     * @param string $proc_id the procedure ID.
     * @return mixed the description of the procedure.
     */
    function get_description($proc_id)
    {
        if (!$this->connected) {
            $this->error = "Error getting description from server: not connected to server.";
            return false;
        }

        fputs($this->sock, "GETDESCRIPTION \"" . $proc_id . '"' . ADDER_DELIM);

        $response = trim(fgets($this->sock));
        if ($response == "GETDESCRIPTION BADPROCEDURE") {
            $this->error = "Error getting description from server: invalid procedure.";
            return false;
        } else {
            preg_match('@GETDESCRIPTION\s*\"(.*)\"@', $response, $matches);
            return $matches[1]; // FIXME
        }
    }

    /**
     * Get the results of a procedure.
     *
     * @param string $proc_id the procedure ID.
     * @return mixed the results of the procedure.
     */
    function get_results($proc_id)
    {
        if (!$this->connected) {
            $this->error = "Error getting results from server: not connected to server.";
            return false;
        }

        fputs($this->sock, 'GETRESULTS2 "' . $proc_id . '"' . ADDER_DELIM);

        $count = MAX_PROCEDURES;
        $response = false;
        while ($count-- > 0) {
            $line = fgets($this->sock);

            if ($line == "GETRESULTS BADPROCEDURE") {
                $this->error = "Error geting results from server: invalid procedure.";
                return false;
            } elseif ($line == "GETRESULTS BADSTAGE") {
                $this->error = "Error getting results from server: election is not yet finished.";
                return false;
            }

            if ($line == "END RESULTS\n") {
                break;
            }

            if ($line != "BEGIN RESULTS\n") {
                $response .= $line;
            }
        }

        if ($response) {
            return $response;
        } else {
            $this->error = "Error getting RESULTS from server: unknown communication error.";
            return false;
        }
    }

    /**
     * Get the list of choices for a procedure.
     *
     * @param string $proc_id the procedure ID.
     * @return mixed the choices of the procedure.
     */
    function get_choices($proc_id)
    {
        if (!$this->connected) {
            $this->error = "Error getting choices from server: not connected to server.";
            return false;
        }

        fputs($this->sock, "GETCHOICES2 \"" . $proc_id . '"' . ADDER_DELIM);

        $count = MAX_CHOICES;
        $response = false;
        while ($count-- > 0) {
            $line = fgets($this->sock);

            if (trim($line) == "GETCHOICES BADPROCEDURE") {
                $this->error = "Error getting choices from server: invalid procedure.";
                return false;
            }

            if ($line == "END CHOICES\n") {
                break;
            }

            if ($line != "BEGIN CHOICES\n") {
                $response .= $line;
            }
        }

        if ($response) {
            $lines = explode("\n", trim($response));
            $choice_count = 0;
            foreach ($lines as $choice) {
                $choices[$choice_count] = explode("~", $choice);
                $choice_count++;
            }

            return $choices;
        } else {
            $this->error = "Error getting choices from server: unknown communication error.";
            return false;
        }
    }

    /**
     * Get all of the authorities public keys from the server.
     *
     * @return mixed the authorities public keys
     */
    function get_auth_pubkeys($procedure)
    {
        if (!$this->connected) {
            $this->error = "Error getting authority public keys from server: not connected to server.";
            return false;
        }

        fputs($this->sock, 'GETAUTHPUBKEYS2 "' . $procedure . '"' . ADDER_DELIM);

        $count = MAX_AUTHORITIES;
        $response = false;
        while ($count-- > 0) {
            $line = fgets($this->sock);

            if (trim($line) == "GETAUTHPUBKEYS BADPROCEDURE") {
                $this->error = "Error getting authority public keys from server: invalid procedure.";
                return false;
            } elseif (trim($line) == "GETAUTHPUBKEYS BADSTAGE") {
                $this->error = "Error getting authority public keys from server: invalid stage.";
                return false;
            }

            if ($line == "END AUTHPUBKEYS\n") {
                break;
            }

            if ($line != "BEGIN AUTHPUBKEYS\n") {
                $response .= $line;
            }
        }

        if ($response) {
            return $response;
        } else {
            $this->error = "Error getting authority public keys from server: unknown communication error.";
            return false;
        }
    }

    /**
     * Get the encrpted sum of the votes from the server.
     *
     * @return mixed the encrypted sum
     */
    function get_cipher_sum($procedure)
    {
        // Fail if there is no connection to server.
        if (!$this->connected) {
            $this->error = "Error getting ciphertext sum from server: not connected to server.";
            return false;
        }

        // Request the public key from the server and return it. Fail on
        // communication error.
        fputs($this->sock, 'GETSUM "' . $procedure . '"' . ADDER_DELIM);
        $response = trim(fgets($this->sock));

        if ($response == "GETSUM BADPROCEDURE") {
            $this->error = "Error getting ciphertext sum from server: invalid procedure.";
            return false;
        } elseif ($response == "GETSUM BADSTAGE") {
            $this->error = "Error getting ciphertext sum from server: bad stage.";
            return false;
        } else {
            preg_match('@GETSUM\s*\"(.*)\"@', $response, $matches);
            return $matches[1]; // FIXME
        }
    }

    /**
     * Return the version of this client interface.
     *
     * @return string the interface protocol version
     */
    function get_client_version()
    {
    	return $this->client_version;
    }

    /**
     * Return the error most recently set by and AdderInterface method.
     *
     * @return string the error message
     */
    function get_error()
    {
        return $this->error;
    }

    /**
     * Get the key constants from the server.
      *
     * @return mixed the key constants
     */
    function get_key_constants($procedure)
    {
        //$key_constants = array('p' => '', 'g' => '', 'h' => '');

        // Fail if there is no connection to server.
        if (!$this->connected) {
            $this->error = "Error getting key constants from server: not connected to server.";
            return false;
        }

        // Request the public key from the server and return it. Fail on
        // communication error.
        fputs($this->sock, 'GETKEYCONSTANTS "' . $procedure . '"' . ADDER_DELIM);
        $response = trim(fgets($this->sock));

        if ($response == "GETKEYCONSTANTS BADPROCEDURE") {
            $this->error = "Error getting key constants from server: invalid procedure.";
            return false;
        } elseif ($response == "GETKEYCONSTANTS NOKEY") {
            $this->error = "Error getting key constants from server: key constants have not yet been created.";
        } else {
            preg_match('@GETKEYCONSTANTS\s*\"(\w*)\"@', $response, $matches);
            return $matches[1]; // FIXME
        }
    }

    /**
     * Get the number of valid votes from the server.
     *
     * @return mixed the number of votes
     */
    function get_num_votes($procedure)
    {
        // Fail if there is no connection to server.
        if (!$this->connected) {
            $this->error = "Error getting ciphertext sum from server: not connected to server.";
            return false;
        }

        // Request the public key from the server and return it. Fail on
        // communication error.
        fputs($this->sock, 'GETNUMVOTES "' . $procedure . '"' . ADDER_DELIM);
        $response = trim(fgets($this->sock));

        if ($response == "GETNUMVOTES BADPROCEDURE") {
            $this->error = "Error getting ciphertext sum from server: invalid procedure.";
            return false;
        } else {
            preg_match('@GETNUMVOTES\s*(\d*)@', $response, $matches);
            return $matches[1]; // FIXME
        }
    }

    /**
     * Get the number of choices from the server.
     *
     * @return mixed the number of choices
     */
    function get_num_choices($proc_id)
    {
        // Fail if there is no connection to server.
        if (!$this->connected) {
            $this->error = "Error getting num choices from server: not connected to server.";
            return false;
        }

        fputs($this->sock, 'GETNUMCHOICES "' . $proc_id . '"' . ADDER_DELIM);
        $response = trim(fgets($this->sock));

        if ($response == "GETNUMCHOICES BADPROCEDURE") {
            $this->error = "Error getting num choices from server: invalid procedure.";
            return false;
        } else {
            preg_match('@GETNUMCHOICES\s*(\d*)\s*(\d*)\s*(\d*)@', $response, $matches);
            return $matches;
        }
    }

    /**
     * Get the private key of the server.
     *
     * @return mixed the private key
     */
    function get_privkey()
    {
        // Fail if there is no connection to server.
        if (!$this->connected) {
            $this->error = "Error getting private key from server: not connected to server.";
            return false;
        }

        // Request the public key from the server and return it. Fail on
        // communication error.
        fputs($this->sock, "GET PRIVKEY" . ADDER_DELIM);
        $response = trim(fgets($this->sock));
        if ($response) {
            return $response;
        } else {
            $this->error = "Error getting private key from server: unkown communication error.";
            return false;
        }
    }

    /**
     * Get the private key components from the server.
     *
     * @return mixed the private key components
     */
    function get_privkey_components($procedure)
    {
        // Fail if there is no connection to server.
        if (!$this->connected) {
            $this->error = "Error getting private key components from server: not connected to server.";
            return false;
        }

        // Request the public key from the server and return it. Fail on
        // communication error.
        fputs($this->sock, 'GETPRIVKEYLIST2 "' . $procedure . '"' . ADDER_DELIM);

        $count = MAX_AUTHORITIES;
        $response = false;
        while ($count-- > 0) {
            $line = fgets($this->sock);

            if (trim($line) == "GETPRIVKEYLIST BADPROCEDURE") {
                $this->error = "Error getting private key components from server: invalid procedure.";
                return false;
            } elseif (trim($line) == "GETPRIVKEYLIST BADSTAGE") {
                $this->error = "Error getting private key components from server: bad stage.";
                return false;
            } elseif (trim($line) == "GETPRIVKEYLIST NOTAUTHORITY") {
                $this->error = "Error getting private key components from server: you are not an authority.";
                return false;
            } elseif (trim($line) == "GETPRIVKEYLIST BADAUTHSTAGE") {
                $this->error = "Error getting private key components from server: you are not allowed to participate in this stage.";
                return false;
            }

            if ($line == "END PRIVKEYLIST\n") {
                break;
            }

            if ($line != "BEGIN PRIVKEYLIST\n") {
                if (!$response) {
                    $response = trim($line);
                } else {
                    $response .= "," . trim($line);
                }
            }
        }

        if ($response) {
            return $response;
        } else {
            $this->error = "Error getting private key components from server: unkown communication error.";
            return false;
        }
    }

    /**
     * Get the list of active procedures from the server.
     *
     * @return mixed an array of the active procedures
     */
    function get_procedure_list()
    {
        if (!$this->connected) {
            $this->error = "Error getting procedure list from server: not connected to server.";
            return false;
        }

        fputs($this->sock, "GETPROCEDURELIST" . ADDER_DELIM);
        $response = fgets($this->sock);

        if (!$response || strlen($response) <= 1) {
            $this->error = "Error getting procedure list from server.";
            return false;
        }

        $procedure_list = Array();

        preg_match('@GETPROCEDURELIST\s*\((.*)\)@', $response, $matches);

        $matches = $matches[1];

        $matches = preg_split("/\),?/", $matches);

        $matches = array_diff($matches, array(""));

        foreach ($matches as $match) {
            $match = trim($match, '(');
            $proc = explode(',', $match);
            $procedure = array('id'             => trim($proc[0], '"'),
                               'title'          => trim($proc[1], '"'),
                               'stage'          => $proc[2],
                               'auths'          => $proc[3],
                               'threshold'      => $proc[4],
                               'robustness'     => $proc[5],
                               'min'            => $proc[6],
                               'max'            => $proc[7]);
            $procedure_list[$procedure['id']]  = $procedure;
        }

        return $procedure_list;
    }

    /**
     * Get the list of public keys from the server.
     *
     * @return mixed an array of the public keys
     */
    function get_pubkey_list($procedure)
    {
        if (!$this->connected) {
            $this->error = "Error getting public key list from server: not connected to server.";
            return false;
        }

        fputs($this->sock, 'GETPUBKEYLIST2 "' . $procedure . '"' . ADDER_DELIM);

        $count = MAX_AUTHORITIES;
        $response = array();
        $i = 0;
        while ($count-- > 0) {
            $line = trim(fgets($this->sock));

            if ($line == "GETPUBKEYLIST BADPROCEDURE") {
                $this->error = "Error getting public key list from server: invalid procedure.";
                return false;
            } elseif ($line == "GETPUBKEYLIST BADSTAGE") {
                $this->error = "Error getting public key list from server: public key submission has not yet begun.";
                return false;
            }

            if ($line == "END PUBKEYLIST") {
                break;
            }

            if ($line != "BEGIN PUBKEYLIST") {
                $response[$i++] = str_replace("'", "", $line);
            }
        }

        if (count($response) > 0) {
            return $response;
        } else {
            $this->error = "Error getting public key list from server: unknown communication error.";
            return false;
        }
    }

    /**
     * Get the list of users from the server.
     *
     * @return mixed an array of the user IDs
     */
    function get_user_list()
    {
        if (!$this->connected) {
            $this->error = "Error getting user list from server: not connected to server.";
            return false;
        }

        fputs($this->sock, "GETUSERLIST2" . ADDER_DELIM);

        $count = MAX_USERS;
        $response = "";
        while ($count-- > 0) {
            $line = fgets($this->sock);

            if ($line == "END USERLIST\n") {
                break;
            }

            if ($line != "BEGIN USERLIST\n") {
                $response .= $line;
            }
        }

        $response = str_replace("'", "", $response);
        $lines = explode("\n", $response);

        if ($response) {
            return $lines;
        } else {
            $this->error = "Error getting user list from server: unknown communication error.";
            return false;
        }
    }

    /**
     * Get the master public key for this procedure from the server.
     *
     * @return mixed the public key
     */
    function get_public_key($procedure)
    {
        // Fail if there is no connection to server.
        if (!$this->connected) {
            $this->error = "Error getting public key from server: not connected to server.";
            return false;
        }

        // Request the public key from the server and return it. Fail on
        // communication error.
        fputs($this->sock, 'GETPUBKEY "' . $procedure . '"' . ADDER_DELIM);
        $response = trim(fgets($this->sock));

        if ($response == "GETPUBKEY BADPROCEDURE") {
            $this->error = "Error getting public key from server: invalid procedure.";
            return false;
        } elseif ($response == "GETPUBKEY BADSTAGE") {
            $this->error = "Error getting public key from server: public key has not yet been created.";
            return false;
        } else {
            preg_match('@GETPUBKEY\s*\"(\w*)\"@', $response, $matches);
            return $matches[1]; // FIXME
        }
    }

    /**
     * Return the version of the server.
     *
     * @return string the protocol version being used by the server
     */
    function get_server_version()
    {
    	return $this->server_version;
    }

    /**
     * Get the stage of the current procedure from the server.
     *
     * @return int the stage of the current procedure or -1 if error
     */
    function get_stage($procedure)
    {

        // Fail if there is no connection to server.
        if (!$this->connected) {
            $this->error = "Error getting stage from server: not connected to server.";
            return -1;
        }

        // Determine which stage of the process the server is in. Store and
        // return the stage number. Fail on communication error.
        fputs($this->sock, 'GETSTAGE "' . $procedure . '"' . ADDER_DELIM);
        $response = fgets($this->sock);

        if (strcmp(trim($response), "GETSTAGE BADPROCEDURE") == 0) {
            $this->error = "Error getting stage from server: invalid procedure.";
            return false;
        } else {
            preg_match('@GETSTAGE\s*(\d*)@', $response, $matches);
            $this->stage = $matches[1]; // FIXME
            return $this->stage;
        }
    }

    /**
     * Get the threshold of authorities for the current procedure from the server.
     *
     * @return int the threshold of authorities
     */
    function get_threshold($procedure)
    {
        // Fail if there is no connection to server.
        if (!$this->connected) {
            $this->error = "Error getting threshold from server: not connected to server.";
            return -1;
        }

        // Get the authority threshold and return it.
        fputs($this->sock, 'GETTHRESHOLD "' . $procedure . '"' . ADDER_DELIM);
        $response = trim(fgets($this->sock));

        if ($response == "GETTHRESHOLD BADPROCEDURE") {
            $this->error = "Error getting threshold hold server: invalid procedure.";
            return -1;
        } else {
            preg_match('@GETTHRESHOLD\s*(\d*)@', $response, $matches);
            return $matches[1]; // FIXME
        }

        return $response;
    }

    /**
     * Get the number of remaining authorities required to advance this stage of the
     * procedure from the server.
     *
     * @return int the remaining number of authorities
     */
    function get_remaining($procedure)
    {
        // Fail if there is no connection to server.
        if (!$this->connected) {
            $this->error = "Error getting remaining from server: not connected to server.";
            return -1;
        }

        // Get the remaining authorities and return it.
        fputs($this->sock, 'GETREMAINING "' . $procedure . '"' . ADDER_DELIM);
        
        $result = trim(fgets($this->sock));
        if ($result == "GETREMAINING BADPROCEDURE") {
            $this->error = "Error getting remaining from server: no such procedure.";
            return false;
        } else {
            preg_match('@GETREMAINING\s*(\d*)@', $result, $matches);
        }

        return $matches[1]; // FIXME
    }

    /**
     * Get the vote of a particular user from the server.
     *
     * @param string $user_id the user id
     * @return mixed the encrypted votes
     */
    function get_vote($procedure, $user_id)
    {
        if (!$this->connected) {
            $this->error = "Error getting vote from server: not connected to server.";
            return false;
        }

        fputs($this->sock, 'GETVOTE "' . $procedure . '" "' . $user_id . '"' . ADDER_DELIM);
        $response = trim(fgets($this->sock));

        if (!strcmp($response, "GETVOTE BADPROCEDURE")) {
            $this->error = "Error getting vote from server: invalid procedure.";
            return false;
        } elseif (!strcmp($response, "GETVOTE BADSTAGE")) {
            $this->error = "Error getting vote from server: voting has not yet begun.";
            return false;
        } elseif (!strcmp($response, "GETVOTE NOVOTE")) {
            $this->error = "Error getting vote from server: user has not voted yet.";
            return false;
        } elseif (!strcmp($response, "GETVOTE INVALIDUSER")) {
            $this->error = "Error getting vote from server: user is invalid.";
             return false;
        } else {
            preg_match('@GETVOTE\s*\"(.*)\"@', $response, $matches);
            return $matches[1]; // FIXME
        }
    }

    /**
     * Get the ballot proof of a particular user from the server.
     *
     * @param string $user_id the user id
     * @return mixed the ballot proof
     */
    function get_ballot_proof($procedure, $user_id)
    {
        if (!$this->connected) {
            $this->error = "Error getting ballot proof from server: not connected to server.";
            return false;
        }

        fputs($this->sock, 'GETBALLOTPROOF "' . $procedure . '" "' . $user_id . '"' . ADDER_DELIM);
        $response = trim(fgets($this->sock));

        if (!strcmp($response, "GETBALLOTPROOF BADPROCEDURE")) {
            $this->error = "Error getting ballot proof from server: invalid procedure.";
            return false;
        } elseif (!strcmp($response, "GETBALLOTPROOF BADSTAGE")) {
            $this->error = "Error getting ballot proof from server: this is not yet the proper stage to retrieve ballot proofs.";
            return false;
        } elseif (!strcmp($response, "GETBALLOTPROOF NOVOTE")) {
            $this->error = "Error getting ballot proof from server: user has not yet voted.";
            return false;
        } elseif (!strcmp($response, "GETBALLOTPROOF INVALIDUSER")) {
            $this->error = "Error getting ballot proof from server: user is invalid.";
            return false;
        } else {
            preg_match('@GETBALLOTPROOF\s*\"(.*)\"@', $response, $matches);
            return $matches[1]; // FIXME
        }
    }

    /**
     * Get the short hash of a particular user from the server.
     *
     * @param string $user_id the user id
     * @return mixed the short hash.
     */
    function get_short_hash($procedure, $user_id)
    {
        if (!$this->connected) {
            $this->error = "Error getting short hash from server: not connected to server.";
            return false;
        }

        fputs($this->sock, 'GETSHORTHASH "' . $procedure . '" "' . $user_id . '"' . ADDER_DELIM);
        $response = trim(fgets($this->sock));

        if (!strcmp($response, "GETSHORTHASH BADPROCEDURE")) {
            $this->error = "Error getting short hash from server: invalid procedure.";
            return false;
        } elseif (!strcmp($response, "GETSHORTHASH BADSTAGE")) {
            $this->error = "Error getting short hash from server: this is not yet the proper stage to retrieve short hashes.";
            return false;
        } elseif (!strcmp($response, "GETSHORTHASH NOVOTE")) {
            $this->error = "Error getting short hash from server: user has not yet voted.";
            return false;
        } else {
            preg_match('@GETSHORTHASH\s*\"(\w*)\"@', $response, $matches);
            return ""; // FIXME $matches[1];
        }
    }

    /**
     * Get a list of the users who have submitted votes for this procedure from
     * the server.
     *
     * @return mixed an array of the user ids
     */
    function get_vote_list($procedure)
    {
        if (!$this->connected) {
            $this->error = "Error getting vote list from server: not connected to server.";
            return false;
        }

        fputs($this->sock, 'GETVOTELIST2 "' . $procedure . '"' . ADDER_DELIM);

        $count = MAX_VOTERS;
        $response = "";
        while ($count-- > 0) {
            $line = fgets($this->sock);
            
            if (trim($line) == "GETVOTELIST BADPROCEDURE") {
                $this->error = "Error getting vote list from server: invalid procedure.";
                return "";
            } elseif (trim($line) == "GETVOTELIST BADSTAGE") {
                $this->error = "Error getting vote list from server: voting has not yet begun.";
                return array();
            }

            if ($line == "END VOTELIST\n") {
                break;
            }

            if ($line != "BEGIN VOTELIST\n") {
                $response .= $line;
            }
        }

        $response = str_replace("'", "", $response);
        $lines = explode("\n", $response);
        if ($response) {
            return $lines;
        } else {
            $this->error = "Error getting vote list from server: unknown communication error.";
            exit();
        }
    }

    /**
     * Get the times as an array of size 5.
     *
     * @return array the array, or an empty array on error
     */
    function get_times($procedure)
    {
        if (!$this->connected) {
            $this->error = "Error getting times from server: not connected to server.";
            return array();
        }

        fputs($this->sock, 'GETTIMES "' . $procedure . '"' . ADDER_DELIM);
        $response = trim(fgets($this->sock));

        if ($response == "GETTIMES BADPROCEDURE") {
            $this->error = "Error getting times from server: invalid procedure.";
            return false;
        } else {
            preg_match('@GETTIMES\s*(\d*)\s*(\d*)\s*(\d*)\s*(\d*)\s*(\d*)@', $response, $matches);
            $times = array(1 => $matches[1], 
                           2 => $matches[2],
                           3 => $matches[3],
                           4 => $matches[4],
                           5 => $matches[5]);
            return $times;
        }
    }

    /**
     * Log in to the server by username/password, and request a session id.
     *
     * @param string $user_id the user id
     * @param string $password the (plaintext) password
     * @param bool $is_authority the variable to hold whether the user is an authority
     * @param string $session_id the variable to hold the session id
     * @return bool true if successful, false otherwise
     */
    function login($user_id, $password, $procedure, &$is_authority, &$session_id)
    {
        // Fail if there is no connection to server.
        if (!$this->connected) {
            $this->error = "Error logging in: not connected to server.";
            return false;
        }

        // Send the login information to the server.
        fputs($this->sock, 'USER "' . $user_id . '" "' . $password . '" "' . $procedure . '"' . ADDER_DELIM);

        // Read the server's response, and return the appropriate message.
        $response = fgets($this->sock);

        if (strcmp(trim($response), "USER BADPROCEDURE") == 0) {
            $this->error = "Error logging in: invalid procedure.";
            return false;
        } elseif (strcmp(trim($response), "USER BADUSER") == 0) {
            $this->error = "Error logging in: invalid name/password.";
            return false;
        } elseif (strcmp(trim($response), "USER BADSTAGE") == 0) {
            $this->error = "Error logging in: this is an authority-only stage, and you are not an authority.";
            return false;
        } else {
            preg_match('@USER\s*(\d*)\s*"(\w*)"@', $response, $matches);
            $is_authority = ($matches[1] == 1);
            $session_id = ($matches[2]);
            return true;
        }
    }

    /**
     * Log out of the server.
     *
     * @param string $session_id the session id
     * @return bool true if successful, false otherwise
     */
    function logout($session_id)
    {
        // Fail if there is no connection to server.
        if (!$this->connected) {
            $this->error = "Error logging out: not connected to server.";
            return false;
        }

        // Send the login information to the server.
        fputs($this->sock, "LOGOUT " . $session_id . ADDER_DELIM);

        // Read the server's response, and return the appropriate message.
        $response = strtoupper(fgets($this->sock));
        $tokens = explode(" ", $response);
        if (strcmp(trim($tokens[1]), "OK") == 0) {
            $this->error = "";
            return true;
        } else {
            $this->error = "Error logging out: invalid session id.";
            return false;
        }
    }

    /**
     * Send the command to start a procedure.
     *
     * @param string $proc_id the id of the procedure to start
     * @return bool true if successful, false otherwise
     */
    function start_procedure ($proc_id)
    {
        // Fail if there is no connection to server.
        if (!$this->connected) {
            $this->error = "Error starting procedure: not connected to server.";
            return false;
        }

        fputs($this->sock, "ADMIN \"password\"" . ADDER_DELIM);
        $response = fgets($this->sock);

        // Send the procedure creation command to the server.
        fputs($this->sock, "STARTPROCEDURE \"" . $proc_id . '"' . ADDER_DELIM);

        // Read the server's response, and return the appropriate message.
        $response = fgets($this->sock);

        if (strcmp(trim($response), "STARTPROCEDURE OK") == 0) {
            $this->error = "";
            return true;
        } elseif (strcmp(trim($response), "STARTPROCEDURE BADPROCEDURE") == 0) {
            $this->error = "Error starting procedure: invalid procedure.";
            return false;
        } elseif (strcmp(trim($response), "STARTPROCEDURE BADSTAGE") == 0) {
            $this->error = "Error starting procedure: this procedure is in a bad stage.";
            return false;
        } else {
            $this->error = "Error starting procedure: unknown communication error.";
            return false;
        }
    }

    /**
     * Advance a procedure.
     *
     * @param string $proc_id the procedure identifier
     * @return bool true if successful or false otherwise
     */
    function progress_procedure($proc_id)
    {
        // Fail if there is no connection to server.
        if (!$this->connected) {
            $this->error = "Error progressing procedure: not connected to server.";
            return false;
        }

        fputs($this->sock, 'ADMIN "password"' . ADDER_DELIM);
        $response = trim(fgets($this->sock));

        fputs($this->sock, 'PROGRESSPROCEDURE "' . $proc_id . '"' . ADDER_DELIM);
        // Read the server's response, and return the appropriate message.
        $response = trim(fgets($this->sock));

        if ($response == "PROGRESSPROCEDURE BADPROCEDURE") {
            $this->error = "Error progressing procedure: invalid procedure.";
            return false;
        } elseif ($response == "PROGRESSPROCEDURE BADSTAGE") {
            $this->error = "Error progressing procedure: procedure is at the final stage.";
            return false;
        } else {
            $this->error = "";
            return true;
        }
    }

    /**
     * Send the command to stop a procedure.
     *
     * @param string $proc_id the id of the procedure to stop
     * @return bool true if successful, false otherwise
     */
    function stop_procedure($proc_id)
    {
        // Fail if there is no connection to server.
        if (!$this->connected) {
            $this->error = "Error stopping procedure: not connected to server.";
            return false;
        }

        fputs($this->sock, 'ADMIN "password"' . ADDER_DELIM);
        $response = trim(fgets($this->sock));

        // Send the procedure stopping command to the server.
        fputs($this->sock, 'STOPPROCEDURE "' . $proc_id . '"' . ADDER_DELIM);

        // Read the server's response, and return the appropriate message.
        $response = fgets($this->sock);

        if (strcmp(trim($response), "STOPPROCEDURE OK") == 0) {
            $this->error = "";
            return true;
        } elseif (strcmp(trim($response), "STOPPROCEDURE BADPROCEDURE") == 0) {
            $this->error = "Error stopping procedure: invalid procedure id.";
            return false;
        } else {
            $this->error = "Error stopping procedure: unknown communication error.";
            return false;
        }
    }

    /**
     * Send the command to delete a procedure.
     *
     * @param string $proc_id the id of the procedure to delete.
     * @return bool true if successful, false otherwise.
     */
    function delete_procedure($proc_id)
    {
        // Fail if there is no connection to server.
        if (!$this->connected) {
            $this->error = "Error deleting procedure: not connected to server.";
            return false;
        }

        fputs($this->sock, 'ADMIN "password"' . ADDER_DELIM);
        $response = trim(fgets($this->sock));

        // Send the procedure deletion command to the server.
        fputs($this->sock, 'DELETEPROCEDURE "' . $proc_id . '"' . ADDER_DELIM);

        // Read the server's response, and return the appropriate message.
        $response = trim(fgets($this->sock));

        if ($response == "DELETEPROCEDURE OK") {
            $this->error = "";
            return true;
        } elseif ($response == "DELETEPROCEDURE BADPROCEDURE") {
            $this->error = "Error deleting procedure: invalid procedure.";
            return false;
        }
    }

    /**
     * Submit a choice (vote).
     *
     * @param int $choice the choice (vote)
     * @return bool true if successful, false otherwise
     */
    function submit_choice ($choice, $proof, $procedure)
    {
        // Fail if there is no connection to server.
        if (!$this->connected) {
            $this->error = "Error submitting choice: not connected to server.";
            return false;
        }

        // Send the public key to the server.
        //        $to_write = strlen('SENDVOTE "' . trim($choice) . '" "' . trim($proof) . '" "' . trim($procedure) . '"' . ADDER_DELIM);
        $bytes = fputs($this->sock, 'SENDVOTE "' . trim($choice) . '" "' . trim($proof) . '" "' . $procedure . '"' . ADDER_DELIM);

        // Read the server's response, and return the appropriate message.
        $response = trim(fgets($this->sock));

        if ($response == "SENDVOTE BADPROCEDURE") {
            $this->error = "Error submitting choice: invalid procedure.";
            return false;
        } elseif ($response == "SENDVOTE BADUSER") {
            $this->error = "Error submitting choice: not logged in.";
            return false;
        } elseif ($response == "SENDVOTE BADSTAGE") {
            $this->error = "Error submitting choice: voting stage is not currently open.";
            return false;
        } elseif ($response == "SENDVOTE DUPLICATE") {
            $this->error = "Error submitting choice: you have already submitted a choice for this procedure.";
            return false;
        } elseif ($response == "SENDVOTE BADVOTE") {
            $this->error = "Error submitting choice: invalid malformed vote.";
            return false;
        } elseif ($response == "SENDVOTE INVALIDPROOF") {
            $this->error = "Error submitting choice: invalid proof.";
            return false;
        } else {
            $this->error = "";
            return true;
        }
    }

    /**
     * Submit a decrypted sum.
     *
     * @param string $sum the decrypted sum
     * @return bool true if successful, false otherwise
     */
    function submit_decrypted_sum($sum, $procedure)
    {
        // Fail if there is no connection to server.
        if (!$this->connected) {
            $this->error = "Error submitting decryption: not connected to server.";
            return false;
        }

        // Send the sum to the server.
        fputs($this->sock, 'SENDSUM ' . $sum . ' "' . $procedure . '"' . ADDER_DELIM);
        $response = trim(fgets($this->sock));

        if ($response == "SENDSUM BADPROCEDURE") {
            $this->error = "Error submitting decryption: invalid procedure.";
            return false;
        } elseif ($response == "SENDSUM BADUSER") {
            $this->error = "Error submitting decryption: bad user.";
            return false;
        } elseif ($response == "SENDSUM BADSTAGE") {
            $this->error = "Error submitting decryption: bad stage.";
            return false;
        } elseif ($response == "SENDSUM DUPLICATE") {
            $this->error = "Error submitting decryption: duplicate.";
            return false;
        } elseif ($response == "SENDSUM BADAUTHSTAGE") {
            $this->error = "Error submitting decryption: bad authority stage.";
            return false;
        } elseif ($response == "SENDSUM OK") {
            $this->error = "";
            return true;
        } else {
            $this->error = "Error submitting decryption: unknown error.";
            return false;
        }
    }

    /**
     * Submit a polynomial.
     *
     * @param string $polynomial the polynomial
     * @return bool true if successful, false otherwise
     */
    function submit_polynomial($polynomial, $gvalues, $procedure)
    {
        // Fail if there is no connection to server.
        if (!$this->connected) {
            $this->error = "Error submitting polynomial: not connected to server.";
            return false;
        }

        $poly_str = '(';

        $poly_list = explode("\n", trim($polynomial));
        foreach ($poly_list as $poly) {
            $poly_str .= "(";
            $pair = explode(" ", $poly);
            $poly_str .= '"' . $pair[0] . '","' . $pair[1] . '"),';
        }
        $poly_str = rtrim($poly_str, ',');
        $poly_str .= ')';

        $gvalue_str = '(';

        $gvalue_list = explode("\n", trim($gvalues));
        foreach ($gvalue_list as $gvalue) {
            $gvalue_str .= "(";
            $pair = explode(" ", $gvalue);
            $gvalue_str .= $pair[0] . ',"' . $pair[1] . '"),';
        }
        $gvalue_str = rtrim($gvalue_str, ',');
        $gvalue_str .= ')';

        // Send the public key to the server.
        fputs($this->sock, 'SENDPOLYLIST ' . $poly_str . ' ' . $gvalue_str . ' "' . $procedure . '"' . ADDER_DELIM);

        // Read the server's response, and return the appropriate message.
        $response = trim(fgets($this->sock));

        if ($response == "SENDPOLYLIST BADPROCEDURE") {
            $this->error = "Error submitting polynomial: invalid procedure.";
            return false;
        } elseif ($response == "SENDPOLYLIST BADUSER") {
            $this->error = "Error submitting polynomial: bad user.";
            return false;
        } elseif ($response == "SENDPOLYLIST BADSTAGE") {
            $this->error = "Error submitting polynomial: you may not submit a polynomial at this stage.";
            return false;
        } elseif ($response == "SENDPOLYLIST BADPOLYLIST") {
            $this->error = "Error submitting polynomial: malformed polynomial.";
            return false;
        } elseif ($response == "SENDPOLYLIST BADAUTHSTAGE") {
            $this->error = "Error submitting polynomial: you are not allowed to participate at this stage.";
            return false;
        } else {
            return true;
        }

    }

    /**
     * Submit a public key.
     *
     * @param string $public_key the public key
     * @return bool true if successful, false otherwise
     */
    function submit_public_key($public_key, $procedure)
    {
        // Fail if there is no connection to server.
        if (!$this->connected) {
            $this->error = "Error submitting public key: not connected to server.";
            return false;
        }

        // Send the public key to the server.
        fputs($this->sock, 'SENDPUBLICKEY "' . $public_key . '" "' . $procedure . '"' . ADDER_DELIM);

        // Read the server's response, and return the appropriate message.
        $response = trim(fgets($this->sock));

        if ($response == "SENDPUBLICKEY BADPROCEDURE") {
            $this->error = "Error submitting public key: invalid procedure.";
            return false;
        } elseif ($response == "SENDPUBLICKEY BADUSER") {
            $this->error = "Error submitting public key: bad user.";
            return false;
        } elseif ($response == "SENDPUBLICKEY BADSTAGE") {
            $this->error = "Error submitting public key: cannot submit a public key at this stage.";
            return false;
        } elseif ($response == "SENDPUBLICKEY DUPLICATE") {
            $this->error = "Error submitting public key: you have already submitted a public key.";
            return false;
        } elseif ($response == "SENDPUBLICKEY BADKEY") {
            $this->error = "Error submitting public key: bad public key.";
            return false;
        } else {
            $this->error = "";
            return true;
        }
    }

    /**
     * Verify that a session id is valid, and return the user id and whether he
     * or she is an authority.
     *
     * @param string $session_id the session id
     * @param string $user_id the variable to hold the user id
     * @param bool $is_authority the variable to hold whether the user is an authority
     * @return bool true is the session is valid, false otherwise
     */
    function verify_session($session_id, $procedure, &$user_id, &$is_authority)
    {
        // Fail if there is no connection to server.
        if (!$this->connected) {
            $this->error = "Error logging in: not connected to server.";
            return false;
        }

        // Send the login information to the server.
        fputs($this->sock, 'SESSION "' . $session_id . '" "' . $procedure . '"' . ADDER_DELIM);

        // Read the server's response, and return the appropriate message.
        $response = trim(fgets($this->sock));

        if ($response == "SESSION BADPROCEDURE") {
            $this->error = "Error logging in: invalid procedure.";
            return false;
        } elseif ($response == "SESSION BADUSER") {
            $this->error = "Error logging in: invalid user.";
            return false;
        } elseif ($response == "SESSION BADSESSION") {
            $this->error = "Error logging in: invalid session.";
            return false;
        } else {
            preg_match('@SESSION\s*(\d*)\s*\"(\w*)\"@', $response, $matches);
            $this->error = "";
            $is_authority = ($matches[1] == 1);
            $user_id = $matches[2];
            return true;
        }
    }
}

?>
