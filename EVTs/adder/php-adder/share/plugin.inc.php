<?php
set_include_path(get_include_path() . PATH_SEPARATOR . '../share');

if (APPLET) {
    require_once 'applet-include.txt';
} else {
    require_once 'plugin-include.txt';
}
?>
