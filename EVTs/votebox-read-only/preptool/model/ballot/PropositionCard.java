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
import preptool.model.ballot.module.TextAreaModule;
import preptool.model.ballot.module.TextFieldModule;
import preptool.model.ballot.module.YesNoOptionsModule;
import preptool.model.language.Language;
import preptool.model.language.LiteralStrings;
import preptool.model.layout.manager.ALayoutManager;
import preptool.model.layout.manager.ALayoutManager.ICardLayout;
import votebox.middle.Properties;

/**
 * PropositionCard is the implementation of an ACard that constitutes a
 * proposition.
 * @author cshaw
 */
public class PropositionCard extends ACard {

    /**
     * Factory to create a PropositionCard
     */
    public static final ICardFactory FACTORY = new ICardFactory() {

        public String getMenuString() {
            return "Add Proposition";
        }

        public ACard makeCard() {
            return new PropositionCard();
        }

    };

    /**
     * Constructs a new RaceCard
     */
    public PropositionCard() {
        super("Proposition");
        modules.add(new TextFieldModule("Title", "Title"));
        modules.add(new TextAreaModule("Description", "Description"));
        modules.add(new YesNoOptionsModule("YesNoOpts"));
    }

    @Override
    public void assignUIDsToBallot(ALayoutManager manager) {
        setUID(manager.getNextBallotUID());
        YesNoOptionsModule optionsModule = (YesNoOptionsModule) getModuleByName("YesNoOpts");
        for (CardElement ce : optionsModule.getData()) {
            ce.setUID(manager.getNextBallotUID());
        }
    }

    @Override
    public String getReviewBlankText(Language language) {
        return LiteralStrings.Singleton.get("NONE", language);
    }

    @Override
    public String getReviewTitle(Language language) {
        TextFieldModule titleModule = (TextFieldModule) getModuleByName("Title");
        return titleModule.getData(language) + ":";
    }

    @Override
    public ICardLayout layoutCard(ALayoutManager manager, ICardLayout cardLayout) {
        Language lang = manager.getLanguage();
        TextFieldModule titleModule = (TextFieldModule) getModuleByName("Title");
        TextAreaModule descriptionModule = (TextAreaModule) getModuleByName("Description");
        YesNoOptionsModule optionsModule = (YesNoOptionsModule) getModuleByName("YesNoOpts");

        cardLayout.setTitle(titleModule.getData(lang));
        cardLayout.setDescription(descriptionModule.getData(lang));
        for (CardElement ce : optionsModule.getData()) {
            cardLayout.addCandidate(ce.getUID(), ce.getName(lang, 0));
        }

        return cardLayout;
    }

    @Override
    public Element toXML(Document doc) {
    	Element cardElt = super.toXML(doc);

    	List<String> ids = new ArrayList<String>();
    	
        YesNoOptionsModule optionsModule = (YesNoOptionsModule) getModuleByName("YesNoOpts");
        for (CardElement ce : optionsModule.getData()) {
            Element cardElementElt = ce.toXML(doc);
            cardElt.appendChild(cardElementElt);
            
            ids.add(ce.uniqueID);
        }
        
        //Need to carry the grouping of these candidates together for NIZK purposes.
        XMLTools.addListProperty(doc, cardElt, Properties.RACE_GROUP, "String", ids.toArray(new String[0]));
        
        return cardElt;
    }
}
