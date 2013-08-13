/**
  * This file is part of VoteBox.
  * 
  * VoteBox is free software: you can redistribute it and/or modify
  * it under the terms of the GNU General Public License version 3 as published by
  * the Free Software Foundation.
  * 
  * You should have received a copy of the GNU General Public License
  * along with VoteBox, found in the root of any distribution or
  * repository containing all or part of VoteBox.
  * 
  * THIS SOFTWARE IS PROVIDED BY WILLIAM MARSH RICE UNIVERSITY, HOUSTON,
  * TX AND IS PROVIDED 'AS IS' AND WITHOUT ANY EXPRESS, IMPLIED OR
  * STATUTORY WARRANTIES, INCLUDING, BUT NOT LIMITED TO, WARRANTIES OF
  * ACCURACY, COMPLETENESS, AND NONINFRINGEMENT.  THE SOFTWARE USER SHALL
  * INDEMNIFY, DEFEND AND HOLD HARMLESS RICE UNIVERSITY AND ITS FACULTY,
  * STAFF AND STUDENTS FROM ANY AND ALL CLAIMS, ACTIONS, DAMAGES, LOSSES,
  * LIABILITIES, COSTS AND EXPENSES, INCLUDING ATTORNEYS' FEES AND COURT
  * COSTS, DIRECTLY OR INDIRECTLY ARISING OUR OF OR IN CONNECTION WITH
  * ACCESS OR USE OF THE SOFTWARE.
 */

package preptool.model.ballot;


import java.util.ArrayList;
import java.util.List;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import preptool.model.XMLTools;
import preptool.model.ballot.module.CandidatesModule;
import preptool.model.ballot.module.TextFieldModule;
import preptool.model.language.Language;
import preptool.model.language.LiteralStrings;
import preptool.model.layout.manager.ALayoutManager;
import preptool.model.layout.manager.ALayoutManager.ICardLayout;
import votebox.middle.Properties;

/**
 * PresidentialRaceCard is the implementation of an ACard that constitutes a
 * race between candidates that have running mates.
 * @author cshaw
 */
public class PresidentialRaceCard extends ACard {

    /**
     * Factory to create a PresidentialRaceCard
     */
    public static final ICardFactory FACTORY = new ICardFactory() {

        public String getMenuString() {
            return "Add Presidential Race";
        }

        public ACard makeCard() {
            return new PresidentialRaceCard();
        }

    };

    /**
     * Constructs a new RaceCard
     */
    public PresidentialRaceCard() {
        super("Presidential Race");
        modules.add(new TextFieldModule("Title", "Title"));
        modules.add(new TextFieldModule("TopOfTicket", "Top Of Ticket"));
        modules.add(new TextFieldModule("BottomOfTicket", "Bottom Of Ticket"));
        modules.add(new CandidatesModule("Candidates", new String[]{
                "Candidate's Name", "Running Mate's Name", "Party" }));
    }

    @Override
    public void assignUIDsToBallot(ALayoutManager manager) {
        setUID(manager.getNextBallotUID());
        CandidatesModule candidatesModule = (CandidatesModule) getModuleByName("Candidates");
        for (CardElement ce : candidatesModule.getData()) {
            ce.setUID(manager.getNextBallotUID());
        }
    }

    @Override
    public String getReviewBlankText(Language language) {
        return LiteralStrings.Singleton.get("NONE", language) + " \n "
                + LiteralStrings.Singleton.get("NONE", language);
    }

    @Override
    public String getReviewTitle(Language language) {
        TextFieldModule topOfTicket = (TextFieldModule) getModuleByName("TopOfTicket");
        TextFieldModule bottomOfTicket = (TextFieldModule) getModuleByName("BottomOfTicket");
        return topOfTicket.getData(language) + " \n "
                + bottomOfTicket.getData(language) + ":";
    }

    @Override
    public ICardLayout layoutCard(ALayoutManager manager, ICardLayout cardLayout) {
        Language lang = manager.getLanguage();
        TextFieldModule titleModule = (TextFieldModule) getModuleByName("Title");
        CandidatesModule candidatesModule = (CandidatesModule) getModuleByName("Candidates");

        cardLayout.setTitle(titleModule.getData(lang));
        for (CardElement ce : candidatesModule.getData()) {
            cardLayout.addCandidate(ce.getUID(), ce.getName(lang, 0), ce
                    .getName(lang, 1), ce.getParty().getAbbrev(lang));
        }
        return cardLayout;
    }

    @Override
    public Element toXML(Document doc) {
    	Element cardElt = super.toXML(doc);

    	List<String> ids = new ArrayList<String>();
    	
        CandidatesModule candidatesModule = (CandidatesModule) getModuleByName("Candidates");
        for (CardElement ce : candidatesModule.getData()) {
            Element cardElementElt = ce.toXML(doc);
            cardElt.appendChild(cardElementElt);
            
            ids.add(ce.uniqueID);
        }
        
        //Need to carry the grouping of these candidates together for NIZK purposes.
        XMLTools.addListProperty(doc, cardElt, Properties.RACE_GROUP, "String", ids.toArray(new String[0]));
        return cardElt;
    }
}
