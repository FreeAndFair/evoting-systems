<?php

// this now needs to go right in the middle of the style section
function writelightlightstyles() {
?>
td {
border: 1px solid white;
background-color: ddffff;
width:15em;
font-size:0.25em;
}

.hidden{
background-color:ffffff;
width:15em;
}

.excluded{
border: 1px solid black;
background-color: ffffff;
width:15em;
}

.high{
background-color: red;
}

.low{
background-color: white;
}

.v0{
background-color: ffffff;
border: 1px solid red;
}

.v1{
background-color: fff0f0;
border: 1px solid red;
}

.v2{
background-color: ffd8d8;
border: 1px solid red;
}

.v3{
background-color: ffb4b4;
border: 1px solid red;
}

.v4{
background-color: ff9090;
border: 1px solid red;
}

.v5{
border: 1px solid red;
background-color: ff6868;
}

.v6{
background-color: ff4040;
border: 1px solid red;
}

.v7{
background-color: ff2020;
border: 1px solid red;
}

.v8{
background-color: ff0000;
border: 1px solid red;
}

<?
}


// this needs to go in the head of the doc.
function writelightlightheadscript($rows,$cols) {

?><script>

function illumeGroup(groupNum) {
  for(var n=1;n<9;n+=2) {
    var funcstring = 'changeClasses(' +groupNum+ ',"v' +n+ '")';
    setTimeout(funcstring,25*n);
    //changeClasses(groupNum,'v8');
  }
}

function extiGroup(groupNum) {
  for(var n=1;n<10;n++) {
    m = 9-n;
    var funcstring = 'changeClasses(' +groupNum+ ',"v' +m+ '")';
    setTimeout(funcstring,25*n);
  }
  setTimeout('returnClasses(' +groupNum+ ');',25*n);
}

function getClassOfId(id) {
  var curr = document.getElementById(id).className;
  return curr;
}

function changeClasses(groupNum,className) {
  nameArr = groupsByNumber[groupNum];
  for(var i=0; i<nameArr.length; i++) {
    document.getElementById(nameArr[i]).className = className;
  }
}

function returnClasses(groupNum) {
  nameArr = groupsByNumber[groupNum];
  for(var i=0; i<nameArr.length; i++) {
    document.getElementById(nameArr[i]).className = originalclasses[nameArr[i]];
  }
}

function extinguish(nameArr) {
  for(var i=0; i<nameArr.length; i++) {
    document.getElementById(nameArr[i]).className = 'low';
  }
}

function illuminate(nameArr) {
    for(var i=0; i<nameArr.length; i++) {
      document.getElementById(nameArr[i]).className = 'high';
    }
}

function extinguish(nameArr) {
  for(var i=0; i<nameArr.length; i++) {
    document.getElementById(nameArr[i]).className = 'low';
  }
} 

function illumeMyGroup(id) {
  num = groupsByName[id];
  illumeGroup(num);
}

groupsByName = new Array();
groupsByNumber = new Array();
originalclasses = new Array();

function group(id,groupNum) {
  if(groupNum==null) groupNum = groupsByNumber.length;
  if(!groupsByNumber[groupNum]) groupsByNumber[groupNum] = new Array();
  groupsByName[id] = groupNum;
  thisline = groupsByNumber[groupNum];
  fields = thisline.length;
  groupsByNumber[groupNum][fields] = id;
  return groupNum;
}

function addGroupByString(str) {
  numbers = str.split(",");
  groupNum = groupsByNumber.length;
  for(var i=0; i<numbers.length; i++) {
    if(numbers[i] != '') {
      var id = numbers[i]+"_"+i;
      group(id,groupNum);
    }
  }
  return groupNum;


}

function setupGroupMousing() {
  for(var groupNum=0; groupNum<groupsByNumber.length; groupNum++) {
    names = groupsByNumber[groupNum];
    for(var i=0;i<names.length;i++) {
      //build original colours table.
      originalclasses[names[i]] = getClassOfId(names[i]);
      document.getElementById(names[i]).onmouseover = new Function("illumeGroup("+groupNum+");");
      document.getElementById(names[i]).onmouseout = new Function("extiGroup("+groupNum+");");
    }
  }


  //colour the excluded links
  for(var i=0;i<rows;i++) {
    for(var j=0;j<cols;j++) {
      var id=i+"_"+j;
      if(groupsByName[id]===undefined) {
        document.getElementById(id).className = "excluded";
      }
    }
  }
}


var rows = <? echo($rows) ?>;
var cols = <? echo($cols) ?>;

document.writeln("<style>\n");
var incr = 255/rows;
var logA = "";
for(var i=0;i<=rows;i++) {
  colorValRG = parseInt(incr*i);
  colorValB = parseInt(255-incr*i);
  
  prefilledRG = "000"+colorValRG.toString(16);
  prefilledB = "000"+colorValB.toString(16);

  pairvalRG = prefilledRG.substr(-2,2);
  pairvalB = prefilledB.substr(-2,2);

  logA += "[" + pairvalRG + "] ";
  var color = pairvalRG+pairvalRG+pairvalB;
  var color2 = pairvalB+pairvalB+pairvalRG;
  document.writeln(".r"+i+" { background-color: #"+color+"; border-color: #"+color2+"} \n");
}
document.writeln("</style>");

</script>
<?
}

/** *******************************
  * writellbody 
  * to write the main body of the page, in particular to 
  *  include the data.
  * Pass in $cslinksArr, structure:
  *  $cslinksArr[$group] = "1,3,4,,3";
  */
function writelightlightbody($cslinksArr) {
?>
<table id="maintable">



<script>
var doinitials = false;
var dofinals = false;
<?
// set up initialTDs and finalTDs if exist
//global $initialTDs, $finalTDs;

if(count($initialTDs)>0) {
  ?> doinitials = true;
  var initialTDs = new Array(); <?
  foreach($initialTDs as $row=>$val) {
    echo("initialTDs[$row] = $val;\n");
  }
}
if(count($finalTDs)>0) {
  ?> dofinals = true;
  var initialTDs = new Array(); <?
  foreach($finalTDs as $row=>$val) {
    echo("finalTDs[$row] = $val;\n");
  }
}
?>

// setup the table headers
document.writeln("<tr>");
if(doinitials) document.writeln("<th>Canonical</th>");
for(var i=0; i<cols*2; i++) {
  document.writeln("<th>&nbsp;&nbsp;&nbsp;&nbsp;</th>");
}
if(dofinals) document.writeln("<th>Ballot</th>");
document.writeln("</tr>");

// setup up the cells themselves
for(var i=0; i<rows; i++) {
  document.writeln("<tr>");
  if(doinitials) document.writeln("<td class='initial'>"+initialTDs[i]+"</td>");
  for(var j=0; j<cols; j++) {
    document.writeln("<td class='hidden'>&nbsp;</td><td id='"+i+"_"+j+"' class='r"+i+"'>&nbsp;</td>");
  }
  if(dofinals) document.writeln("<td class='final'>"+finalTDs[i]+"</td>");
  document.writeln("</tr>\n");
}

document.writeln("</table>\n");

var groupNum;
<?

$i=0;
foreach($cslinksArr as $group => $cslist) {
  $i++;
  ?>groupNum = addGroupByString("<?
  echo($cslist);
  ?>");
  changeClasses(groupNum,"r<? echo($i) ?>");
  <?

}


?>
setupGroupMousing();

</script>
<?
}





?>