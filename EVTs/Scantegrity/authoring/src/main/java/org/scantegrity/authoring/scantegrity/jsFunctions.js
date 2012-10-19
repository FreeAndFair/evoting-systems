/*
Sumary of fields
_Q_A stands for race (question) Q, candidate (answer) A
race_Q - the text for the race number Q
candidate_Q_A - text field for candidate A in race Q

topSymbol_Q_A - text field with the symbol(s) that appears on the top page 
voteTop_Q_A - button (transparent) for voting the candidates on the top page

bottomSymbol_Q_R_A - text field with the symbol(s) that appear on the bottom page
voteBottom_Q_R_A - button (orange disk) for voting for the symbols on the bottom page
orangeTop_Q_R_A - orange mark on the top page
orangeBottom_Q_R_A - orange mark on the bottom page
orangeBoth_Q_R_A - orange mark on both pages

doneWithSelection - button (text "Done") to be pressed when all the candidates have been selected
*/

init();

function init() {
	hideOrange();

    for (q=0;q<noq;q++) {
        rows = 1;
        if (qType[q]=="rank") {
        	rows=maxAPerQ[q];
        }
        for (a=0;a<noa[q];a++) {
		    for (r=0;r<rows;r++) {
			      if (r==0)
		              getField("bottomSymbol_"+q+"_"+r+"_"+a).display=display.visible;
	              getField("voteBottom_"+q+"_"+r+"_"+a).display=display.visible;
   	              getField("topHole_"+q+"_"+r+"_"+a).display=display.visible;
		    }            
        }
		vote[q]=new Array(maxAPerQ[q]);
		for (r=0;r<vote[q].length;r++) {
			vote[q][r]=-1;
		}        
    }

    for (s=0;s<noDigitsInSerial;s++) {
		getField("serialTop_"+s).display=display.visible;    			
    }
    
    //getField("doneWithSelection0").display=display.visible;
    //getField("doneWithSelection1").display=display.visible;    
}

function hideOrange() {
    for (q=0;q<noq;q++) {
        rows = 1;
        if (qType[q]=="rank") {
        	rows=maxAPerQ[q];
        }
        for (a=0;a<noa[q];a++) {
		    for (r=0;r<rows;r++) {
	              getField("topHole_"+q+"_"+r+"_"+a).display=display.hidden;
	              getField("orangeBoth_"+q+"_"+r+"_"+a).display=display.hidden;	              	              	              
		    }            
        }
    }
}

function voteOne(q,a) {
	console.println(makeXMLVote());
	//If a vote is clicked again, it deselects
	if (getField("orangeBoth_"+q+"_0_"+a).display==display.visible) {
		getField("orangeBoth_"+q+"_0_"+a).display=display.hidden;		
	    vote[q][0]=-1;
	    return;
	}
	
	//deselect the selected one and select the new one
	console.println("orangeBoth_"+q+"_0_"+vote[q][0]);
	if (vote[q][0]!=-1)
		getField("orangeBoth_"+q+"_0_"+vote[q][0]).display=display.hidden;

    vote[q][0]=a;
	getField("orangeBoth_"+q+"_0_"+a).display=display.visible;	    
}

function voteMany(q,a) {
	console.println(makeXMLVote());
	//If a vote is clicked again, it deselects
	if (getField("orangeBoth_"+q+"_0_"+a).display==display.visible) {
		getField("orangeBoth_"+q+"_0_"+a).display=display.hidden;		
	    vote[q][0]=-1;
	    return;
	}

	//check if the maximum number of candidates have been selected
	max=vote[q].length;
	for (r=0;r<vote[q].length;r++) {
		console.println("vote "+vote[q][r]);	
		if (vote[q][r]==-1) {
			max--;
		}
	}

	//if no more votes can be selected, simply return
	if (max==vote[q].length)
		return;
	
	//mark the selected vote
	for (r=0;r<vote[q].length;r++) {
		if (vote[q][r]==-1) {
			vote[q][r]=a;
			getField("orangeBoth_"+q+"_0_"+a).display=display.visible;					
			return;
		}
	}
}

function voteRank(q,r,a) {
	console.println(makeXMLVote());
	//If a vote is clicked again, it deselects
	if (getField("orangeBoth_"+q+"_"+r+"_"+a).display==display.visible) {
		getField("orangeBoth_"+q+"_"+r+"_"+a).display=display.hidden;		
	    vote[q][r]=-1;
	    return;
	}
	
	//check if the same answer is not allready selected (column unicity)
	for (rr=0;rr<vote[q].length;rr++) {
		if (vote[q][rr]==a) {
			//if the row does not have anything selected, move the mark automatically
			if (vote[q][r]==-1) {
				vote[q][rr]=-1;
				getField("orangeBoth_"+q+"_"+rr+"_"+a).display=display.hidden;		
				vote[q][r]=a;
				getField("orangeBoth_"+q+"_"+r+"_"+a).display=display.visible;								
			}
			return;
		}
	}

	//check if the rank is not taken (row unicity)
	if (vote[q][r]!=-1) {
		//if the column does not have anything selected, move the mark automatically 
		for (rr=0;rr<maxAPerQ[q];rr++) {
			if (vote[q][rr]==a) {
				return;
			}
		}
		getField("orangeBoth_"+q+"_"+r+"_"+vote[q][r]).display=display.hidden;
		getField("orangeBoth_"+q+"_"+r+"_"+a).display=display.visible;
		vote[q][r]=a;
		return;
	}

	
	//mark the selected vote	
	vote[q][r]=a;
	getField("orangeBoth_"+q+"_"+r+"_"+a).display=display.visible;						
}

function finishSelection()
{
//TODO for each contest, set all the letters to the selected ones
    for (q=0;q<noq;q++) {
    	if (maxAPerQ[q]==1) {
    		
    	}
    }


//app.mailMsg(true, "poste@gwu.edu", "", "", "PunchScan Ballot", makeCompactXMLVote());


//this.print({bUI: true,bSilent: true,bShrinkToFit: true});
}

function hideSymbols(page) {
    if (page=="bottom") {
	    for (q=0;q<noq;q++) {
	        for (a=0;a<noa[q];a++) {        
	        	getField("topSymbol_"+q+"_"+a).display=display.hidden;
	        }
	    }
	} else {
	    for (q=0;q<noq;q++) {
	        rows = 1;
	        if (qType[q]=="rank") {
	        	rows=vote[q].length;
	        }
	        for (r=0;r<rows;r++) {
		        for (a=0;a<noa[q];a++) {        
		        	getField("bottomSymbol_"+q+"_"+0+"_"+a).display=display.hidden;
		        }
		    }
	    }	
	}
}


function makeXMLVote() {
	serial="";
    for (s=0;s<noDigitsInSerial;s++) {
		serial=serial+getField("serialTop_"+s).value;    	
    }
	s="<xml><ballot id=\""+serial+"\">\n";
		
    for (q=0;q<noq;q++) {
		s+="\t<q"+q+">\n";    
        for (r=0;r<vote[q].length;r++) {
			s+="\t\t<dot>"+vote[q][r]+"</dot>\n";
		}
		s+="\t</q"+q+">\n";
	}
	s+="</ballot></xml>\n";
	return s;
}

function makeCompactXMLVote() {
	serial="";
    for (s=0;s<noDigitsInSerial;s++) {
		serial=serial+getField("serialTop_"+s).value;    	
    }
    s="";
	s+=serial;
	
    for (q=0;q<noq;q++) {
        for (r=0;r<vote[q].length;r++) {
        	s+=" ";
        	if (vote[q][r]!=-1)
        		s+=getField("bottomSymbol_"+q+"_"+0+"_"+vote[q][r]).value;
        	else
				s+=vote[q][r];
		}
	}
	return s;
}