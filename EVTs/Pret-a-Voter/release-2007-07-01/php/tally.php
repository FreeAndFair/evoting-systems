<?php

/** ********************************
  * tally.php
  * Tally looks up the result of a finished election.
  *
  * Method
  * . Check the election has finished
  * . Retrieve all the lines from the database
  * . Calculate the loser each round
  * . Present to the user
  */



  // includes
  include_once("config.php");

  // Get the debug switch
  if(isset($_GET['debug'])) {
    $debug = $_GET['debug'];
  } else {
    $debug = 0;
  }

  // do head of html page
  $titleprefix = "Election Tally";
  if($debug) $titleprefix .= " - debug";
  include("header.php");


?><div id="mainlinks">
<a href="receiptlookup.php">Receipt Lookup</a><br />
<a href="auditedballot.php">Audited Ballot Lookup</a><br />
<a href="tellerlinks.php">Teller Links Audit</a><br />
<a href="tally.php">Election Tally</a><br />
  </div>
    <div id="mainvider">
      <!-- nowt -->&nbsp;
    </div>
    <div id="maincontent">
      <div id="maintitle">Election Tally</div>
<?


  /** TODO: CHECK THAT THE ELECTION HAS FINISHED */

  // Retrieve all the lines of the database

  foreach($racesArr as $race => $candidates) {


    if($debug) echo("<hr>race: $race<br /><br />\n");
    $sql = "SELECT tally_round,candidate_id,tally_votes FROM tallies where election_id=0 and race_id=$race";
    $res = $db->queryArr($sql);

    $racedata = array();


    foreach($res as $row=>$data) {
      $tallyround = $data["tally_round"];
      $candidate = $data["candidate_id"];
      $tally_votes = $data["tally_votes"];

      if(!is_array($racedata[$tallyround])) $racedata[$tallyround] = array();

      $racedata[$tallyround][$candidate] = $tally_votes;

    }

    if($debug) {
      echo("queried db: $sql <br />res: $res<br />");
      echo("res etc: <br />");
      print_r($racedata);
    }

    $verbose = '';

    // count for a single race
    echo("<div><h3>Race ".($race+1)." ".$race_titles[$race].":</h3>\n");
    
//    if($race_types[$race] == 'stv') {

      echo("<table><tr>");
      if($race_types[$race] == 'stv') echo("<th><b>Round</b></th>");

      // show the candidate names
      for($i=0;$i<count($races_candidates[$race]);$i++) {
        echo("<th>".$races_candidates[$race][$i]."</th>\n");
      }
      echo("</tr>");

      foreach($racedata as $round => $candArr) {
        echo("<tr>");
        if($race_types[$race] == 'stv')
                 echo("<td style='border-right: 1px solid black'><i>$round</i></td>");

        for($candidate = 0; $candidate<$candidates; $candidate++) {
          $votes = $candArr[$candidate];
          if($votes == -1) {
            if($round == 1) $votes = "X";
            elseif($racedata[$round-1][$candidate]!= -1) $votes = "X";
            else $votes = " ";
          }
          echo("<td>$votes</td>");
        }

        echo("</tr>\n");

      }

      echo("</table></div><div><p>&nbsp;</p></div>");

 //   } else {
     // not stv, therefore ox







    //  echo("<div><p>&nbsp;</p><p>&nbsp;</p></div>");


 //   }
      echo("<div><p>&nbsp;</p><p>&nbsp;</p></div>");

  }

/*****************************************************
  if($debug) echo("Reconstructing votes");

  $votesData = array();
  $votes = array();
  foreach($receipt_ids as $row=>$receipt_id) {
    $votesData[$receipt_id] = new Rec("receipts");
    $votesData[$receipt_id]->retrieveById($receipt_id);
    $votestring = $votesData[$receipt_id]->get("partialform_permstring");
    $race = $votesData[$receipt_id]->get("race_id");
    if(!is_array($votes[$race])) $votes[$race] = array();
    if($race_types[$race] == "stv") {
      $votes[$race][$receipt_id] = invertOrder($votestring);
    } else {
      $votes[$race][$receipt_id] = $votestring;
    }
  }

  if($debug) {
    print_r($votes);
    echo("<br />Tallying<br />\n");
  }


  foreach($votes as $race=>$raceArr) {
    $verbose = '';

    // count for a single race
    echo("<h3>Race [$race] ".$race_titles[$race].":</h3>\n");

    // before actually counting, determine the quota for each race.
    $sql = "SELECT COUNT(*) FROM receipts WHERE race_id=$race AND teller_id=0 AND teller_batch=1 LIMIT 1";
    $res = $db->queryArr($sql);
    $result = $res[0];
    foreach($result as $key=>$val) $count = $val;
    $quota = $val/2;
    //echo("Quota for this race is $quota<br />\n"); 

// *****************************************************

    // count each race, depending on the race type
    if($race_types[$race] == 'stv') {
      echo("<table><tr><th><b>Round</b></th>");
      // how many have a first choice for candidate X?
      $forcandidate = array();
      for($i=0;$i<count($races_candidates[$race]);$i++) {
        $forcandidate[$i]=0;
        echo("<th>".$races_candidates[$race][$i]."</th>\n");
      }
      echo("</tr>");

      $flagDone = false;
      // while not finished
      $round = 1;
      while(!$flagDone && ($round<50)) {

        echo("<tr>");
        // wipe the slate for the remaining candidates (-1 indicates they're out)
        $remainingcandidates = 0;
        $quota = 0;
        $flagDeadHeat = false;
        $flagWon = false;
        unset($winners);
        for($i=0;$i<count($races_candidates[$race]);$i++) {
          if($forcandidate[$i]>-1) {
            $forcandidate[$i]=0;
            $remainingcandidates++;
          }
        }

        echo("<td><b>$round</b></td>\n");
        $verbose .= "<b>Round $round</b><br />\n";

        // for each vote, add their next choice to the tally
        foreach($raceArr as $receipt_id=>$votestring) {
          $thisvote = $votestring[0]-1;
          if($forcandidate[$thisvote]>-1) {
            $forcandidate[$thisvote]++;
            $quota += 1/2;
          }
        }
        $verbose .= "Quota for this round is $quota <br />\n";

        // see if anyone has won, if so, flag it
        foreach($forcandidate as $candidate => $numvotes) {
          echo("<td>");
          if($debug) echo("Candidate '$candidate': $numvotes<br />\n");
          if($numvotes>$quota) {
            echo("<b>$numvotes</b>");
            $flagDone = true;
            $winner = $candidate;
            $flagWon = true;
          } elseif($remainingcandidates==2) {
            // dead heat to win
            $flagDone = true;
            $flagDeadHeat = true;
            if(!is_array($winners)) $winners = array();


            // if this is one of the winners, add them to the list.
            if($numvotes > 0) {
              $winners[] = $candidate;
              echo("<i>$numvotes</i>");
            } 
          } else {
            if($numvotes>-1) echo($numvotes);
            // ANY OTHER CONDITIONS REGARDING ABSOLUTE NUMBER OF VOTES GO HERE
          }
          echo("</td>");
        }

        echo("</tr>");
        // noone has won then see if anyone can be eliminated.
        if(!$flagDone) {
          $loser = -1;
          $min = 2*$quota;
          reset($forcandidate);
          foreach($forcandidate as $candidate => $numvotes) {
            if($debug) echo("cand: $candidate, vot: $numvotes ... ");
            if($numvotes > -1) {
              if($debug) echo(" > -1 <br />\n");
              if($numvotes < $min) {
                $min = $numvotes;
                $loser = $candidate;
              } elseif($numvotes == $min) {
                // DEAD HEAT FOR LOSING GOES HERE
              }
            } else {
              //echo(" <= -1 <br />\n");
            }
          }

          $verbose .= "Loser this time is: [$loser] ".$races_candidates[$race][$loser].", with ".$forcandidate[$loser]." votes<br />\n";

          // if someone is being eliminated, nullify the candidate option
          $forcandidate[$loser] = -1;
        }

        // for each vote, if their next choice was an eliminated candidate, lop the front off.
        if(!$flagDone) {
          foreach($raceArr as $receipt_id => $votestring) {
            $flagStopLopping = false;
            while(!$flagStopLopping) {
              if(strlen($votestring) > 0) {
                $nextchoice = $votestring[0];
                if($debug) echo("receipt: $receipt_id, next: $nextchoice ... ");
                if($forcandidate[$nextchoice] == -1) {
                  $votestring = substr($votestring,1);
                  $raceArr[$receipt_id] = $votestring;
                  if($debug) echo(" -> $votestring<br />\n");
                } else {
                  // next choice is ok, signal stop
                  $flagStopLopping = true;
                  if($debug) echo(" |<br />\n");
                }
              } else {
                //run out of next choices... what happens now? 
                //  reduce the quota, unset the array? This is the
                //  don't-waste-my-vote point
                if($debug) echo("receipt: $receipt_id is exhausted<br />\n");
                $flagStopLopping = true;
              }
            } //end while
          } //end foreach
        } //end if

      $round++;
      }// end while

      $round--;
      // declare/print the STV result
      if($flagWon) {
        echo($verbose."This race was won outright in round $round by [$winner] ".$races_candidates[$race][$winner]." <Br />\n");
      } elseif($flagDeadHeat) {
        echo($verbose."Noone passed the quota to gain a majority by the time this came down to 2 candidates. Their votes in the final round are:<br />\n");
        foreach($forcandidate as $candidate => $numvotes) {
          if($numvotes > -1) echo("Candidate [$candidate] ".$races_candidates[$race][$candidate].": $numvotes <br />\n");
        }
      }

      echo("</table>");

    } else {
      echo("Referendum:<br />");

      // initialise variables
      $blankvotecount = 0;
      $forcandidate = array();
      for($i=0;$i<count($races_candidates[$race]);$i++) $forcandidate[$i] = 0;

      // rank options by number of votes
      foreach($raceArr as $receipt_id => $votestring) {
        // find the x
        $xpos = strpos($votestring,"x");

        // sanity check
        if($xpos === false) {
          // no vote
          $blankvotecount++;
        } else {
          // increment this total
          $forcandidate[$xpos]++;
        }
      }
      echo("Blank votes:$blankvotecount<br />\n");

      // sort the ranks
      arsort($forcandidate,SORT_NUMERIC);

      // declare any winner and print result
      echo("<br />Vote count in descending order:<br />\n");
      foreach($forcandidate as $candidate=>$numvotes) {
        echo("[$candidate] ".$races_candidates[$race][$candidate].": $numvotes<br />\n");
      }


    }


  }

  // */




  include('footer.php');

?>