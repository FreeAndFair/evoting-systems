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


import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import preptool.model.Party;
import preptool.model.XMLTools;
import preptool.model.language.Language;
import preptool.model.layout.manager.ALayoutManager;

/**
 * A Ballot is the model's notion of the entire ballot itself. It contains a
 * list of cards ({@link ACard}) that hold information about each race or
 * choice the user must make on the ballot. Note that there are some choices
 * that the user makes that are not within the ballot, such as the user's
 * language. These are implemented purely in the Layout.
 * @author cshaw
 */
public class Ballot {

    /**
     * Parses XML into a Ballot object
     * @param elt the element
     * @return the Ballot
     */
    public static Ballot parseXML(Element elt) {
        assert elt.getTagName().equals("Ballot");
        Ballot ballot = new Ballot();
        ArrayList<String> languageNames = new ArrayList<String>();
        NodeList list = elt.getChildNodes();
        for (int i = 0; i < list.getLength(); i++) {
            Node child = list.item(i);
            if (child.getNodeName().equals("Card"))
                ballot.getCards().add(ACard.parseXML((Element) child));
            else if (child.getNodeName().equals("Language"))
                languageNames.add(((Element) child).getAttribute("name"));
            else if (child.getNodeName().equals("Party"))
                ballot.getParties().add(Party.parseXML((Element) child));
        }
        for (Language lang : Language.getAllLanguages())
            if (languageNames.contains(lang.getName()))
                ballot.getLanguages().add(lang);
        ballot.fixParties();
        return ballot;
    }

    /**
     * An array of cards contained on this Ballot.
     */
    private ArrayList<ACard> cards;

    /**
     * The languages in the ballot
     */
    private ArrayList<Language> languages;

    /**
     * The parties in the ballot (may not all be used)
     */
    private ArrayList<Party> parties;

    /**
     * Constructs a blank Ballot with an empty list of cards.
     */
    public Ballot() {
        cards = new ArrayList<ACard>();
        languages = new ArrayList<Language>();
        parties = new ArrayList<Party>();
    }

    /**
     * Assigns the UIDs to the ballot elements
     * @param manager the layout manager
     */
    public void assignUIDsToBallot(ALayoutManager manager) {
        for (ACard card : cards)
            card.assignUIDsToBallot(manager);
    }

    /**
     * @return the cards
     */
    public ArrayList<ACard> getCards() {
        return cards;
    }

    /**
     * @return the languages
     */
    public ArrayList<Language> getLanguages() {
        return languages;
    }

    /**
     * @return the parties
     */
    public ArrayList<Party> getParties() {
        return parties;
    }

    /**
     * @param languages the languages to set
     */
    public void setLanguages(ArrayList<Language> languages) {
        this.languages = languages;
    }

    /**
     * Converts this ballot to a savable XML representation, to be opened later
     * @param doc the document
     * @return the element for this Ballot
     */
    public Element toSaveXML(Document doc) {
        Element ballotElt = doc.createElement("Ballot");
        for (Language lang : languages) {
            Element langElt = doc.createElement("Language");
            langElt.setAttribute("name", lang.getName());
            ballotElt.appendChild(langElt);
        }
        for (Party party : parties)
            ballotElt.appendChild(party.toSaveXML(doc));
        for (ACard c : cards) {
            Element cardElt = c.toSaveXML(doc);
            ballotElt.appendChild(cardElt);
        }
        return ballotElt;
    }

    /**
     * Converts this ballot to an XML representation
     * @param doc the document
     * @return the element for this Ballot
     */
    public Element toXML(Document doc) {
        Element ballotElt = doc.createElement("Ballot");
        XMLTools.addProperty(doc, ballotElt, "StartImageSize", "Integer", "1");

        String[] langArray = new String[languages.size()];
        for (int i = 0; i < languages.size(); i++)
            langArray[i] = languages.get(i).getShortName();
        XMLTools.addListProperty(doc, ballotElt, "Languages", "String", langArray);
        XMLTools.addProperty(doc, ballotElt, "MaxImageSize", "Integer", "1");
        for (ACard c : cards) {
            Element cardElt = c.toXML(doc);
            ballotElt.appendChild(cardElt);
        }
        return ballotElt;
    }

    /**
     * Updates references in candidates' parties so they are all the same as the
     * parties in the ballot
     */
    public void fixParties() {
        for (ACard card: cards)
            card.fixParties(parties);
    }
}
