<?php 

include_once("config.php");

function abbrev($string) {
  // for now, just take the first 25 characters
  $str = $string;
  //$str = substr($string, 0, 22)."...";

  return $str;
}

function no_nasties($querypiece) {
  // lose the DROP, INSERT, etc

  $check = strtolower($querypiece);
  if(!strstr("drop",$check) && !strstr("insert",$check) && !strstr("update",$check)) {
    $return = $querypiece;
  } else {
    $return = false;
  }

  return $return;
}

// receiptHTML returns a chunk of html showing a ballot with the data from a receiptstring in it
// basically a wrapper for ballotHTML taking a receiptvotestring argument.
function receiptHTML($receiptvotestring) {
  // put receiptvotes in usable array
  $receiptvotes = explode(",",$receiptvotestring);

  /**  ***** Fill the boxesdata array **************** */
  $boxesdata = array();

  global $racesArr;



  foreach($racesArr as $race=>$candidates) {
   
    /* example:
     * $boxesdata[0] = array( 	1=>"a1",
				2=>"a2",
				3=>"a3");  */

    $boxesdata[$race] = array();
 
    for($i=1;$i<=$candidates;$i++) {
      $thisval = $receiptvotes[$race][$i];

      /** TODO: Do any kind of processing, like converting to image version 
        *    -> translateVoteMarks func (in collection) */
      $htmlcontents = translateVoteMarks($thisval);

      $boxesdata[$race][$i] = $htmlcontents;
    }

  }

  // spit out all the HTML for this ballot form
  $ret = ballotHTML($boxesdata);

  return $ret;
}



// ballotHTML returns a chunk of html which shows a ballot with boxesdata in it
// $boxesdata[ballotnum][line]   (ballotnum:- 0 to races-1, line:- 1 to $candidates)
function ballotHTML($boxesdata) {
  global $racesArr;
  global $h_gap;

  // Need to get details of the races. 
  /** TODO: code to generate the array goes here */

  // Determine total height. Gap between each race:
  $total = 0;
  foreach($racesArr as $race => $candidates) {
    $total += $candidates + $h_gap;
  }
  $height_unit = 100/$total;


  // Seed the random number generator (for the bg colors)
  srand(7538);


  // Generate the div structure
  $html .= '<div id="ballot">';
  $colour = 0;

//  global $races;

  foreach($racesArr as $race => $candidates) {
    $html .= miniballotHTML($race, $boxesdata[$race], $height_unit);
  }

  $html .= "</div>\n";
  return $html;
}




// miniballotHTML($miniballotdata) returns a chunk of html 
//  which shows a mini ballot with miniballotdata in it
// $miniballotdata[line]
function miniballotHTML($race, $miniballotdata, $height_unit) {
  global $racesArr;
  global $race_types;
  global $race_titles;
  global $h_gap;

  $type = $race_types[$race];

  //retrieve previous data for this race;
  //if($flag_review) 
  //$prev = $prevs[$race];
  

  $candidates = $racesArr[$race];



  // write out the candidate box, each race with a different background shade
  $colour = dechex(rand(225,253)).dechex(rand(225,253)).dechex(rand(225,255));

  $mini = '<div class="race" style="background-color:#'.$colour.'; ';
  $mini .= 'height:'.($height_unit * $candidates).'%; padding-top:'.($height_unit*$h_gap).'%;">';
  $mini .= '<div class="racename" style="height:100%">'.$race_titles[$race].'</div>';
  $mini .= '<div class="candidatebox" style="height:100%;">';

  // HTML for a candidate choice
  //for($i=1;$i<=$candidates;$i++) {
  foreach($miniballotdata as $i => $thisval) {
    $elem_name = "race{$race}_{$i}";
    $mini .= "    <div class='candidate' style='height:".(100/$candidates)."%;border-bottom:1px solid grey'>\n";

    $mini .= $thisval;

    $mini .= "    </div>\n";

  }

  $mini .= "  </div>\n</div>\n";


  return $mini;
}

/** translateVoteMarks exists to move from a numerical value to 
  *  the html etc wanted to display the value on the webpage
  */
function translateVoteMarks($markchar) {
  
  // Define translation array for values -> html for boxes
  $pre = "<img src='images/";
  $post = ".gif' style='height:100%' />";
  $translate = array(	"1" => $pre."1".$post,
			"2" => $pre."2".$post,
			"3" => $pre."3".$post,
			"4" => $pre."4".$post,
			"5" => $pre."5".$post,
			"6" => $pre."6".$post,
			"-" => $pre."-".$post,
			"x" => $pre."x".$post,
			"o" => $pre."o".$post    );

  return $translate[$markchar];

}


/** permute 
  * Takes an ordering (array e.g. 0,3,1,2),
  * applies the permutation (array e.g. 1,3,2,0) and 
  * returns the resulting order (0312 p 1320 -> 2013)
  */
function permute($order, $permutation) {

global $debug;

  if($debug) echo("ENTER: old:".print_r($order).",perm:".print_r($permutation)."<br />");

  /** $neworder = array(); //$order;
  // for each term in the permutation
  //   get the term in the order at that position, in
  //   the original order and add it to the list
  foreach($permutation as $newpos => $oldpos) {

    
    if($debug) echo("newpos: $newpos, oldpos: $oldpos, val:".$order[$oldpos]."<br />");
    //$neworder[$newpos] = $order[$oldpos];
    $neworder[$oldpos] = $order[$newpos];
  }
  if($debug) print_r($neworder);

  //$neworder = array_flip($neworder);
  if($debug) print_r($neworder);
  //sort($neworder);

*/

  // find the 0 in permutation[], find the value at the same index in order, put in 

  $interim = array_flip($permutation);

  if($debug) echo("presort Interim:".print_r($interim)."<br />");

  ksort($interim);

  if($debug) echo("postsort Interim:".print_r($interim)."<br />");

  foreach($interim as $key => $val) {
    if($debug) echo("key:$key, val:$val, to:".$order[$val]."<br />");

    $neworder[$key] = $order[$val];
  }

  if($debug) echo("old:".print_r($order).",new:".print_r($neworder)."<br />");

  return $neworder;
}

/** permuteWithPipes
  * Wrapper for permute that takes a permutation that is pipe-separated
  */
function permuteWithPipes($order,$pipeseparatedpermutation) {
global $debug;
  $permutation = explode("|",$pipeseparatedpermutation);

  if($debug) echo("withpipes:$pipeseparatedpermutation<br />\n");
  return permute($order,$permutation);
}


/** invertOrder
  * inverts order from a votestring. So 51342 becomes 25341
  */
function invertOrder($order) {

  $neworder = '';

  //echo("order: $order<br />\n");
  for($i=1;$i<=$order.length;$i++) {
    $pos = strpos($order,$i."");
    if($pos === false) {
      $i=$order.length;
    } else {
      $neworder .= $pos+1;
    }
  }
  //echo("neworder: $neworder<br />");

  return $neworder;
}

?>