<?php

$filename = "http://131.227.68.245/index.php?csv=77777,a1b2c3d4e5,5e4d3c2b1a,1-2,12,123,-1,1-,ox,xo";
//"/usr/local/something.txt";
$handle = fopen($filename, "r");
$contents = fread($handle, filesize($filename));
sleep(5);
fclose($handle);

?>

