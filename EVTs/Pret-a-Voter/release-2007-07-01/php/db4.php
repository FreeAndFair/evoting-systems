<?php

/** db4.php 
  * database class, container for all the database functions etc.
  * requires config.php to have set the variables in the constructor:
  * host, username, password, databasename, 
  * [optional] port.
  * TODO: add optional socket
  */

class db {

  // Define a database connection variable $pConnection;
  var $pConnection = 0;
  var $pHost;
  var $pUsername;
  var $pPassword;
  var $pDatabaseName;
  var $pPort;
  
  /** Constructor. Only works in PHP5. */
  function __construct($host,$username,$password,$dbname,$port = false) {
    $this->pHost = $host;
    $this->pUsername = $username;
    $this->pPassword = $password;
    $this->pDatabaseName = $dbname;
    $this->pPort = $port ? $port : false;
  }

  /** Fake constructor for PHP4 */
  function construct($host,$username,$password,$dbname,$port = false) {
    $this->pHost = $host;
    $this->pUsername = $username;
    $this->pPassword = $password;
    $this->pDatabaseName = $dbname;
    $this->pPort = $port ? $port : false;
    return $this;
  }

  /** PHP4 real constructor */
  function db($host,$username,$password,$dbname,$port = false) {
    $this->construct($host,$username,$password,$dbname,$port = false);
  }

  /** db->connect connects to the database with the parameters
    * already set in config.php. Use db->connectifnot to 
    * reuse any existing connection (below).
    */
  function connect() {
    //var $sqli;			//hold the connection to be returned
  
    if ($this->pPort > 0) {
      $sqlink = mysql_connect($this->pHost, $this->pUsername, $this->pPassword)
        or die("Could not connect: ".mysql_error());
      mysql_select($this->pDatabaseName) or die("Could not select database"); //, $this->pPort);
    } else {
      $sqlink = mysql_connect($this->pHost, $this->pUsername, $this->pPassword)
        or die("Could not connect: ".mysql_error());
      mysql_select_db($this->pDatabaseName) or die("Could not select database");
    }

    // Check for errors, straight off the php.net mysqli-connect doc:
    if(mysql_errno($sqlink)) {
      // TODO: Think properly about whether to really write the error to the screen.
      printf("Connect failed: %s\n", mysql_error($sqlink));

      // Could exit here, but risks not trying hard enough.
      $this->pConnection = 0;
      //exit();
      return false;

    } else {  //No errors

      //echo("Connected, no errors");
       // Set the global connection variable, return it.
      $this->pConnection = $sqlink;
      return $sqlink;
    }

  }

  /** db->connectIfNot is intended to attempt to
    * connect to the database only if there is 
    * no existing connection. Returns a mysql link 
    * object, whether a pre-existing or new one.
    */
  function connectIfNot() {
    //Check global parameter
    if($this->pConnection) {
      return $this->pConnection;
    } else {
      /** Attempt to connect. Do we ever want this to not die 
        * at the first attempt?
        */
      $this->pConnection = $this->connect() or die("Could not connect to database");

      return $this->pConnection;
    }
  }

  /** db->disconnect simply closes the db->connection
    * if it's open. preferably only put this in the 
    * footers/destruct commands at the end. Returns
    * the output of mysql_close if the connection
    * existed, or -1 if there was no connection.
    */
  function disconnect() {
    if($this->pConnection) {
      return mysql_close($this->pConnection);
    } else {
      return -1;
    }
  }

  /** db->query handles all queries for 
    * the database. Ideally just make the 
    * connection variable accessible here.
    * Returns the result object (which would
    * ideally be closed at some point), or 
    * false on failure. 
    * TODO: Put maliciousness checking here.
    */
  function query($mysqlquery) {

    // Get the link, if it's not already alive.
    $link = $this->connectIfNot();

    //echo("Query: $mysqlquery<br />");
    // Return result, or false on failure
    if ($result = mysql_query($mysqlquery,$link)) {
      return $result;
    } else {
      return false;
    }

  }

  /** queryArr functions similarly to query, but if the result exists, it retrieves the entire 
    * result, frees the resource, and returns the resulting array. Do not use when most
    * of the result won't be used, but do use when you will get all of the result anyway.
    */
  function queryArr($sql) {

    // Use the normal query function to get the result object
    $res = $this->query($sql);

    // Decant into an array object, free up and return.
    if($res) {
      while($row = mysql_fetch_array($res,MYSQL_ASSOC)) {
        $arr[] = $row;
      }
      mysql_free_result($res);
      return $arr;
    } else {
      // Assume this is survivable.
      return false;
    }
  }


}