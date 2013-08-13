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
import java.util.Observer;


import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;

import preptool.controller.exception.BallotOpenException;
import preptool.model.Party;
import preptool.model.XMLTools;
import preptool.model.ballot.module.AModule;
import preptool.model.ballot.module.CandidatesModule;
import preptool.model.ballot.module.TextFieldModule;
import preptool.model.language.Language;
import preptool.model.layout.manager.ALayoutManager;
import preptool.model.layout.manager.ALayoutManager.ICardLayout;


/**
 * An ACard is the abstract representation of a choice that the user must make,
 * that lies in the ballot. For instance, a race for Mayor or a proposition to
 * cut taxes would be represented using an ACard. An ACard contains a list of
 * AModules, which contain information specific to the type of card, i.e. a
 * title or a list of candidates
 * @author cshaw
 */
public abstract class ACard {

    /**
     * Parses an XML element into an ACard
     * @param elt the element
     * @return the ACard
     */
    public static ACard parseXML(Element elt) {
        assert elt.getTagName().equals("Card");
        ACard card;
        if (elt.getAttribute("type").equals("Race"))
            card = new RaceCard();
        else if (elt.getAttribute("type").equals("Presidential Race"))
            card = new PresidentialRaceCard();
        else if (elt.getAttribute("type").equals("Proposition"))
            card = new PropositionCard();
        else
            throw new BallotOpenException("Unknown card type: "
                    + elt.getAttribute("type"));
        card.modules.clear();

        NodeList list = elt.getElementsByTagName("Module");
        for (int i = 0; i < list.getLength(); i++) {
            Element child = (Element) list.item(i);
            card.modules.add(AModule.parseXML(child));
        }

        return card;
    }

    protected String uniqueID;
    
    protected String titleLabelID = "";

    protected String type;

    protected ArrayList<AModule> modules;

    /**
     * Constructs a blank ACard with an empty list of modules.
     */
    public ACard(String type) {
        this.type = type;
        this.modules = new ArrayList<AModule>();
    }

    /**
     * Adds an observer to the module with the given name, if it exists
     * @param moduleName the name of the module to add the observer to
     * @param obs the observer to add to the module
     */
    public void addModuleObserver(String moduleName, Observer obs) {
        AModule module = getModuleByName(moduleName);
        if (module != null) module.addObserver(obs);
    }

    /**
     * Assigns the UIDs to this card
     * @param manager the layout manager
     */
    public abstract void assignUIDsToBallot(ALayoutManager manager);

    /**
     * Looks for a module with the given name in this cards list of modules, and
     * returns it if it exists, null otherwise
     * @param name the name of the module to lookup
     * @return the module if it exists
     */
    public AModule getModuleByName(String name) {
        for (AModule m : modules)
            if (m.getName().equals(name)) return m;
        return null;
    }

    /**
     * Returns the list of modules that contain information and behavior for
     * this card
     * @return the modules
     */
    public ArrayList<AModule> getModules() {
        return modules;
    }

    /**
     * Returns the text to show on the review screen if the user has not made a
     * selection on this card
     * @param language the language
     */
    public abstract String getReviewBlankText(Language language);

    /**
     * Returns the review title for this card
     * @param language the language
     * @return the review title
     */
    public abstract String getReviewTitle(Language language);

    /**
     * Returns this card's title, by checking to see if there is a title module
     * and returning its data. If there is no title, returns the empty string
     * @param lang the language to get the title in
     * @return the title, if any
     */
    public String getTitle(Language lang) {
        AModule module = getModuleByName("Title");
        if (module != null)
            return ((TextFieldModule) module).getData(lang);
        else
            return "";
    }

    /**
     * Returns the type name (as a String) of this ballot, i.e. Race
     * @return the type
     */
    public String getType() {
        return type;
    }

    /**
     * Returns the unique ID of this card, set by the LayoutManager when
     * exporting.
     */
    public String getUID() {
        return uniqueID;
    }

    /**
     * Lays out this card in the given ICardLayout
     * @param manager the layout manager
     * @param cardLayout the card layout object
     * @return the finished card layout object
     */
    public abstract ICardLayout layoutCard(ALayoutManager manager,
            ICardLayout cardLayout);

    /**
     * Returns whether this card needs translation information for the given
     * language
     * @param lang the language to check
     * @return true if translations are needed, false otherwise
     */
    public boolean needsTranslation(Language lang) {
        boolean res = false;
        for (AModule m : modules)
            res |= m.needsTranslation(lang);
        return res;
    }

    /**
     * Sets the unique ID of this card
     * @param uid the unique ID to set
     */
    public void setUID(String uid) {
        uniqueID = uid;
    }
    
    public void setTitleID(String titleID){
    	titleLabelID = titleID;
    }

    /**
     * Formats this ACard as a savable XML element
     * @param doc the document
     * @return this ACard as an Element
     */
    public Element toSaveXML(Document doc) {
        Element cardElt = doc.createElement("Card");
        cardElt.setAttribute("type", type);

        for (AModule m : modules)
            cardElt.appendChild(m.toSaveXML(doc));

        return cardElt;
    }

    /**
     * Formats this ACard as a VoteBox XML element
     * @param doc the document
     * @return this ACard as an Element
     */
    public Element toXML(Document doc){
    	Element cardElt = doc.createElement("Card");
        cardElt.setAttribute("uid", uniqueID);
        XMLTools.addProperty(doc, cardElt, "CardStrategy", "String",
                "RadioButton");
        
        XMLTools.addProperty(doc, cardElt, "TitleLabelUID", "String",
        		titleLabelID);
        
        
        return cardElt;
    }

    /**
     * Updates references in candidates' parties so they are all the
     * same as the parties in the ballot.
     */
    public void fixParties(ArrayList<Party> parties) {
        AModule m = getModuleByName("Candidates");
        if (m != null) {
            CandidatesModule candidates = (CandidatesModule) m;
            ArrayList<CardElement> elements = candidates.getData();
            for (CardElement elt : elements) {
                int idx = parties.indexOf(elt.getParty());
                if (idx != -1) elt.setParty(parties.get(idx));
            }
        }
    }
}
