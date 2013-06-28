<?php // test php

function foo($a,$b) {
  echo("a:$a, b:$b<br />\n");
}

?>
foo(1,5):<?
foo(1,5);

?>
foo(1) = 5:<?
foo(1) = 5;

function bar($a,$b,$c,$d) {
  echo("a:$a, b:$b, c:$c, d:$d<br />\n");
}

?>
bar(1,2,3,4):<?
bar(1,2,3,4);

?>
bar(1,2,3) = 4:<?
bar(1,2,3) = 4;


?>