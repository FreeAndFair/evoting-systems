<?php

/** Rec class holds an array of fields, which can have a name, a value, a column name (for
  * the database), and an indexOfTable (containing the name of the table it is the index of).
  */

include_once("fieldclass4.php");
include_once("functioncollection.php");
include_once("megastructure.php");

class Rec {
  var $fields = array();
  var $table;
  var $keyfield;
  //fields["Id"] = new Field(0,"table_id",$this->table);

  // Constructor. Takes tablename, looks up structure in $megastructure
  function Rec($tablename) {
    $this->table = $tablename;
    global $megastructure;
    $this->fields = $megastructure[$tablename];

    //find key
    foreach($this->fields as $fieldname => $field) {
      if($field->get("type") == "key") {
        $this->keyfield = $fieldname;
        $field->set("keyOfTable",$tablename);
      }
    }
  }

  // set & get for Table name, read only.
  function setTable($name) {
    return $this;
  }
  
  function getTable() {
    return $this->table;
  }

  // isKeyOfTable returns name of table for which $fieldname is the key.
  function isKeyOfTable($fieldname) {
    return $this->fields[$fieldname]->get("keyOfTable");
  }

  // getKeyName retrieves the name of the field which is key of this table
  function getKeyName() {
    return $this->keyfield;
  }

  // getKey gets the unique key of this record in the table
  function getKey() {
    return $this->fields[$this->keyfield]->get("value");
  }

  // countFields counts the number of fields in the table
  function countFields() {
    return count($this->fields);
  }

  /** Get & set for the fields array's values. 
    */
  function get($fieldname) {
    if(isset($this->fields[$fieldname])) {
      return $this->fields[$fieldname]->get("value");
    } else return false;
  }

  function set($fieldname,$value) {
    if(isset($this->fields[$fieldname])) {
      $this->fields[$fieldname]->set("value",$value);
      return $this;
    }
  }

  // retrieveById fills the field from the database, given the key.
  function retrieveById($key) {
    global $db;

    // construct query
    $sql = "SELECT * FROM ".$this->table." WHERE ".$this->keyfield."=$key LIMIT 1";
    $res = $db->queryArr($sql);

    foreach($res[0] as $fieldname => $value) {
//       echo("fieldname: $fieldname, value: $value<br />");
      $this->fields[$fieldname]->set("value",$value);
    }

    return $this;
  }

  // retrieveById fills the field from the database, given the key.
  function retrieveByManyIds($keysArr) {
    global $db,$debug;

    // construct query
    $sql = "SELECT * FROM ".$this->table." WHERE ";
    foreach($keysArr as $key=>$testval) {
      $ands[] .= "$key=$testval";
    }
    $sql .= implode(" AND ",$ands);
    $sql .= " LIMIT 1";

    if($debug) echo("retrieveByManyIds: sql: $sql<br />\n");
    $res = $db->queryArr($sql);

    foreach($res[0] as $fieldname => $value) {
//       echo("fieldname: $fieldname, value: $value<br />");
      $this->fields[$fieldname]->set("value",$value);
    }

    return $this;
  }

  

  /** getHTMLRow returns an html table row containing all the data,
   *    unless it is a blob or a long text. For a long text, it gives
   *    the abbrev(string) (global) characters, for a blob it gives a link
   *    to the file and abbrev(string) characters of the hex. */
  function getHTMLRow() {
    $html = "<tr>\n";

    // go through each field, adding a td for each.
    foreach($this->fields as $fieldname => $field) {
      $html .= "  <td>";

      $value = $field->get("value");

      // can we link this to a further info type page
      if($field->get("keyOfTable")) {
        $oftable = $field->get("keyOfTable");
        $html .= "<a href='$furtherinfopage?table=$oftable&highlight=$value'>";
      }

      // deal with different data types
      $type = $field->get("type");

      if($type == "text") {
        $html .= abbrev($value);
      } elseif($type == "blob") {
        $html .= abbrev(bin2hex($value));
      } else {
        $html .= $value;
      }

      if($field->get("keyOfTable")) $html .= "</a>";

      $html .= "</td>\n";
    }

    return $html;
  }

  function getVerboseRow() {
    $verb = "";

    // go through each field, adding a td for each.
    foreach($this->fields as $fieldname => $field) {

      $verb .= $fieldname.": ";
      $value = $field->get("value");

      // deal with different data types
      $type = $field->get("type");

      if($type == "text") {
        $verb .= abbrev($value);
      } elseif($type == "blob") {
        $verb .= abbrev(bin2hex($value));
      } else {
        $verb .= $value;
      }

      if($field->get("keyOfTable")) $html .= "</a>";

      $html .= "</td>\n";
    }

    return $html;
  }

}

?>