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

var chosenPage="none";
var DocPrefs= {
    DoDialog: function(){return app.execDialog(this);},
    strGRP1:"",
    GetRadioSel:function(oRslts,aCtrls){
      for(var strRtn=aCtrls[0];aCtrls.length>0;strRtn=aCtrls.pop()){
        if(oRslts[strRtn] == true)
          return strRtn;
      }
      return "";
    },
    commit: function(dialog)
    {
        var oRslt = dialog.store();
        this.strGRP1 = this.GetRadioSel(oRslt,["Rad1","Rad2"]);
    },
    description:
    {
        name:"Please choose a group of letters to keep",
        elements:
        [
            {
                type: "static_text",
                item_id: "stat",
                name: "Please choose a group of letters to keep",
                char_width: 15,
                alignment: "align_fill",
                font: "dialog",
            },
            {
                type: "cluster",
                elements:
                [
                    {
                        type: "radio",
                        item_id: "Rad1",
                        group_id: "tb",
                        name: "Erase horizontal letters",
                    },
                    {
                        type: "radio",
                        item_id: "Rad2",
                        group_id: "tb",
                        name: "Erase vertical letters",
                    },
                    {
                        type: "ok_cancel", 
                    }
                ]
            }
        ]
    }
}

init();

welcome();

function welcome() {
	app.alert("                                          WELCOME\n\nYou’ll be able to vote this ballot using your computer and then must\nprint it out on a piece of paper, sign it in ink, and fax or mail it in.\n\nThe steps in more detail are as follows:\n1. Click your choice of candidate (these highlight when you fly over them\nand can be unselected by clicking again.)\n2. Click the “proceed to ballot casting” button.\m3. Click either the “horizontal” or “vertical” letters button and the\nother letters will disappear.\n4. print out your ballot (a black and white or color print either letter\nsize or A4).\n5. Fill and sign the “affidavit” part of the form in ink.\n6. You must either mail in or fax in your signed form for it to be\ncounted (to the number and or address on the ballot).\n7. Once your ballot is received, you'll be able to check online that it was\nscanned and recorded properly by checking the position marked (and also\nthat the PDF was correct by checking that the letters are the same).");
	//app.alert("To ensure your privacy, only half of the letters appearing on this ballot will be returned. There are two groups of letters appearing both to the left and to the right of the choices. It does not affect your vote which group you keep.");
}

function init() {
	hideOrange();

    for (q=0;q<noq;q++) {
        rows = 1;
        if (qType[q]=="rank") {
        	rows=maxAPerQ[q];
        }
        for (a=0;a<noa[q];a++) {
            getField("topSymbol_"+q+"_"+a).display=display.visible;
            getField("voteTop_"+q+"_"+a).display=display.visible;
		    for (r=0;r<rows;r++) {
	              getField("bottomSymbol_"+q+"_"+r+"_"+a).display=display.visible;
	              getField("voteBottom_"+q+"_"+r+"_"+a).display=display.visible;
		    }            
        }
		vote[q]=new Array(maxAPerQ[q]);
		for (r=0;r<vote[q].length;r++) {
			vote[q][r]=-1;
		}        
    }

    for (s=0;s<noDigitsInSerial;s++) {
		getField("serialTop_"+s).display=display.visible;    	
		getField("serialBottom_"+s).display=display.visible;    			
    }
    
    //getField("doneWithSelection0").display=display.visible;
    getField("doneWithSelection1").display=display.visible;    
}

function hideOrange() {
    for (q=0;q<noq;q++) {
        rows = 1;
        if (qType[q]=="rank") {
        	rows=maxAPerQ[q];
        }
        for (a=0;a<noa[q];a++) {
		getField("highlightCandidate_"+q+"_"+a).display=display.hidden;        
		    for (r=0;r<rows;r++) {
	              getField("orangeTop_"+q+"_"+r+"_"+a).display=display.hidden;
	              getField("topHole_"+q+"_"+r+"_"+a).display=display.hidden;
	              getField("orangeBottom_"+q+"_"+r+"_"+a).display=display.hidden;
	              getField("orangeBoth_"+q+"_"+r+"_"+a).display=display.hidden;	              	              	              
		    }            
        }
    }
}

function getCandidateSelected(q,letter) {
	for (aa=0;aa<noa[q];aa++) {
        if (letter==getField("topSymbol_"+q+"_"+aa).value) {
        	return aa;
        }
    }
    return -1;
}

function voteOne(q,a) {	
	candidate=getCandidateSelected(q,getField("bottomSymbol_"+q+"_0_"+a).value);
	//If a vote is clicked again, it deselects
	if (getField("orangeBoth_"+q+"_0_"+a).display==display.visible) {
		getField("orangeBoth_"+q+"_0_"+a).display=display.hidden;
		getField("highlightCandidate_"+q+"_"+candidate).display=display.hidden;
	    vote[q][0]=-1;
	    return;
	}
	
	//deselect the selected one and select the new one
	if (vote[q][0]!=-1) {
		getField("orangeBoth_"+q+"_0_"+vote[q][0]).display=display.hidden;
		oldcandidate=getCandidateSelected(q,getField("bottomSymbol_"+q+"_0_"+vote[q][0]).value);		
		getField("highlightCandidate_"+q+"_"+oldcandidate).display=display.hidden;
	}

	getField("orangeBoth_"+q+"_0_"+a).display=display.visible;	    
	getField("highlightCandidate_"+q+"_"+candidate).display=display.visible;	
    vote[q][0]=a;	
}

function voteMany(q,a) {
	candidate=getCandidateSelected(q,getField("bottomSymbol_"+q+"_0_"+a).value);
//	console.println("bottomSymbol_"+q+"_0_"+a);
//	console.println(getField("bottomSymbol_"+q+"_0_"+a).value);
//	console.println(q+" "+candidate);

	//If a vote is clicked again, it deselects
	if (getField("orangeBoth_"+q+"_0_"+a).display==display.visible) {
		getField("orangeBoth_"+q+"_0_"+a).display=display.hidden;
		getField("highlightCandidate_"+q+"_"+candidate).display=display.hidden;		
	    vote[q][0]=-1;
	    return;
	}

	//check if the maximum number of candidates have been selected
	max=vote[q].length;
	for (r=0;r<vote[q].length;r++) {
//		console.println("vote "+vote[q][r]);	
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
			getField("orangeBoth_"+q+"_0_"+a).display=display.visible;
			getField("highlightCandidate_"+q+"_"+candidate).display=display.visible;			
			vote[q][r]=a;			
			return;
		}
	}
}

function voteRank(q,r,a) {
	candidate=getCandidateSelected(q,getField("bottomSymbol_"+q+"_"+r+"_"+a).value);
//	console.println("bottomSymbol_"+q+"_"+r+"_"+a);
//	console.println(getField("bottomSymbol_"+q+"_"+r+"_"+a).value);
//	console.println(q+" "+candidate);

	//If a vote is clicked again, it deselects
	if (getField("orangeBoth_"+q+"_"+r+"_"+a).display==display.visible) {
		getField("orangeBoth_"+q+"_"+r+"_"+a).display=display.hidden;
		getField("highlightCandidate_"+q+"_"+candidate).display=display.hidden;				
	    vote[q][r]=-1;
	    return;
	}
	
	//check if the same answer is not allready selected (column unicity)
	for (rr=0;rr<vote[q].length;rr++) {
		if (vote[q][rr]==a) {
			//if the row does not have anything selected, move the mark automatically
			if (vote[q][r]==-1) {
				oldcandidate=getCandidateSelected(q,getField("bottomSymbol_"+q+"_"+rr+"_"+vote[q][rr]).value);
				getField("highlightCandidate_"+q+"_"+oldcandidate).display=display.hidden;
				getField("orangeBoth_"+q+"_"+rr+"_"+a).display=display.hidden;
				vote[q][rr]=-1;
								
				
				getField("orangeBoth_"+q+"_"+r+"_"+a).display=display.visible;
				getField("highlightCandidate_"+q+"_"+candidate).display=display.visible;
				vote[q][r]=a;
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
		oldcandidate=getCandidateSelected(q,getField("bottomSymbol_"+q+"_"+r+"_"+vote[q][r]).value);
		getField("highlightCandidate_"+q+"_"+oldcandidate).display=display.hidden;		
		
		getField("orangeBoth_"+q+"_"+r+"_"+a).display=display.visible;
		getField("highlightCandidate_"+q+"_"+candidate).display=display.visible;				
		vote[q][r]=a;
		return;
	}

	
	//mark the selected vote	
	getField("orangeBoth_"+q+"_"+r+"_"+a).display=display.visible;						
	getField("highlightCandidate_"+q+"_"+candidate).display=display.visible;	
	vote[q][r]=a;		
}

function voteTop(q,a)
{
    mark = getField("topSymbol_"+q+"_"+a).value;

    for (aa=0;aa<noa[q];aa++) {
        if (mark==getField("bottomSymbol_"+q+"_0_"+aa).value) {
			if (qType[q]=="one") {
				voteOne(q,aa);
				return;
			}
			if (qType[q]=="many") {
				voteMany(q,aa);
				return;
			}
			//qType=="rank"
			//find the first nonselected rank
			for (rr=0;rr<maxAPerQ[q];rr++) {
				if (vote[q][rr]==-1) {
	            	voteRank(q,rr,aa);
	            	return;
	            }
				if (vote[q][rr]==aa) {
	            	voteRank(q,rr,aa);
	            	return;
	            }	            
	        }
		    return;
        }
    }
}

function finishSelection()
{
	DocPrefs.strGRP1 = "";
	if("ok" != DocPrefs.DoDialog())
	{
	    return
	}

    if (DocPrefs.strGRP1=="Rad1") {
        choosePage("top");
    } else {
        choosePage("bottom");
    }
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
		        	getField("bottomSymbol_"+q+"_"+r+"_"+a).display=display.hidden;
		        }
		    }
	    }	
	}
}

function choosePage(page)
{
	chosenPage=page;
	
	hideOrange();
    hideSymbols(page);
	
   for (q=0;q<noq;q++) {
        rows = 1;
        if (qType[q]=="rank") {
        	rows=maxAPerQ[q];
        }
        for (a=0;a<noa[q];a++) {
            getField("voteTop_"+q+"_"+a).display=display.hidden;        
		    for (r=0;r<rows;r++) {
	            getField("voteBottom_"+q+"_"+r+"_"+a).display=display.hidden;
				//if (page=="top") getField("topHole_"+q+"_"+r+"_"+a).display=display.visible;	            
			}
		}
	}

    //getField("doneWithSelection0").display=display.hidden;
    getField("doneWithSelection1").display=display.hidden;
		
    orange="orangeTop";
    if (page=="bottom")
    	orange="orangeBottom";
    for (q=0;q<noq;q++) {
        for (r=0;r<vote[q].length;r++) {
	        a=vote[q][r];
	        if (a!=-1) {
	        	if (qType[q]=="many")
		            getField(orange+"_"+q+"_"+0+"_"+a).display=display.visible;
		        else
		        	getField(orange+"_"+q+"_"+r+"_"+a).display=display.visible;
	        }
	    }            
    }

    serial="serialTop";
    if (page=="top")
    	serial="serialBottom";
    
    for (s=0;s<noDigitsInSerial;s++) {
		getField(serial+"_"+s).display=display.hidden;    	
    }
    
//app.mailMsg(true, "poste@gwu.edu", "", "", "PunchScan Ballot", makeXMLVote());


	this.print({bUI: true,bSilent: true,bShrinkToFit: true});
}

function makeXMLVote() {
	serial="";
    for (s=0;s<noDigitsInSerial;s++) {
		serial=serial+getField("serialTop_"+s).value;    	
    }
	s="<xml><ballot id=\""+serial+"\" type=\""+chosenPage+"\">\n";
		
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
    if (chosenPage=="top")
    	s+="T";
    else
    	s+="B";
	s+=serial;
	
    for (q=0;q<noq;q++) {
        for (r=0;r<vote[q].length;r++) {
        	s+=" ";
			s+=vote[q][r];
		}
	}
	return s;
}