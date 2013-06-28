<?php

/** Field class holds a field, which can have a name, a value and a column name (for
  * the database).
  */

class Field {
  var $data;

  // Constructor
  function Field($type,$desc) {
    $this->data = array("type"=>false,
			"value"=>false,
			"desc"=>false,
			"keyOfTable"=>false);
  

    $this->data["type"] = $type;
    $this->data["desc"] = $desc;
  }

  function get($member) {
    if (isset($this->data[$member])) {
      return $this->data[$member];
    }
  }

  function set($member, $value) {
    if (isset($this->data[$member])) {
      $this->data[$member] = $value;
      return $this;
    }
  }

}

?>