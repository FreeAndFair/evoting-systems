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


import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;

import preptool.model.Party;
import preptool.model.language.Language;
import preptool.model.language.LocalizedString;

/**
 * A CardElement is an option that the user has to choose from, that lies in the
 * ballot. For instance, candidates in a race would be represented using
 * CardElements.
 * @author cshaw
 */
public class CardElement {

	/**
	 * Parses XML into a CardElement object
	 * @param elt the element
	 * @param names number of names in the new CardElement
	 * 
	 * @return the CardElement
	 */
	public static CardElement parseXML(Element elt, int names) {
		assert elt.getTagName().equals("CardElement");
		CardElement ce = new CardElement(names);

		NodeList list = elt.getElementsByTagName("LocalizedString");
		for (int i = 0; i < list.getLength(); i++) {
			Element child = (Element) list.item(i);
			if (child.getAttribute("name").equals("Name" + i))
				ce.names[i] = LocalizedString.parseXML(child);
		}

		list = elt.getElementsByTagName("Party");
		if (list.getLength() > 0)
			ce.party = Party.parseXML((Element) list.item(0));
		return ce;
	}

	protected String uniqueID;

	protected int numNames;

	protected LocalizedString[] names;

	protected Party party;

	/**
	 * Creates a new CardElement, with the given number of names
	 * @param num the number of names
	 */
	public CardElement(int num) {
		numNames = num;
		names = new LocalizedString[numNames];
		for (int i = 0; i < numNames; i++) {
			names[i] = new LocalizedString();
		}
		party = Party.NO_PARTY;
	}

	/**
	 * Creates a new CardElement with a single name, and sets the given
	 * LocalizedString to that name
	 * @param str the LocalizedString for the name
	 */
	public CardElement(LocalizedString str) {
		numNames = 1;
		names = new LocalizedString[1];
		names[0] = str;
		party = Party.NO_PARTY;
	}

	/**
	 * Copies all names to the given language from the primary language
	 * @param lang the language to copy to
	 * @param primary the primary language
	 */
	public void copyFromPrimary(Language lang, Language primary) {
		for (int i = 0; i < numNames; i++)
			names[i].set(lang, names[i].get(primary));
	}

	/**
	 * Gets the data for the given language and column number. If the column
	 * number is within numNames, that name is returned as a String. If it is
	 * the next column, the party is returned
	 * @param lang the language
	 * @param idx the column index
	 * @return the data for this column
	 */
	public Object getColumn(Language lang, int idx) {
		if (idx == numNames)
			return getParty();
		else
			return getName(lang, idx);
	}

	/**
	 * Returns the name for the given index
	 * @param lang the language
	 * @param idx the index
	 * @return the name
	 */
	public String getName(Language lang, int idx) {
		return names[idx].get(lang);
	}

	/**
	 * @return the numNames
	 */
	public int getNumNames() {
		return numNames;
	}

	/**
	 * @return the party
	 */
	public Party getParty() {
		return party;
	}

	/**
	 * @return the unique ID of this Card Element, set by the LayoutManager when
	 *         exporting.
	 */
	public String getUID() {
		return uniqueID;
	}

	/**
	 * Returns whether or not this card element is missing translation
	 * information for the given language
	 * @param lang the language
	 * @return the result
	 */
	public boolean needsTranslation(Language lang) {
		return false;
	}

	/**
	 * Sets the column to the given data.  See {@link #getColumn(Language, int)} for explanation
	 * on column numbers.  If the party column is specified, but the data is
	 * "Edit...", then the user has selected the Edit parties option, and this
	 * call is ignored.
	 * @param lang the language
	 * @param idx the column number
	 * @param val the data
	 */
	public void setColumn(Language lang, int idx, Object val) {
		if (idx == numNames) {
			if (val.equals("Edit...")) // this is the edit parties dialog
				// option, just ignore it
				return;
			party = (Party) val;
		} else
			names[idx].set(lang, (String) val);
	}

    /**
     * Sets the party
     */
    public void setParty(Party p) {
        party = p;
    }
    
	/**
	 * @param uid the unique ID to set
	 */
	public void setUID(String uid) {
		uniqueID = uid;
	}

	/**
	 * Converts this element to a savable XML representation, to be opened later
	 * @param doc the document
	 * @return the element for this card element
	 */
	public Element toSaveXML(Document doc) {
		Element cardElementElt = doc.createElement("CardElement");
		for (int i = 0; i < numNames; i++)
			cardElementElt.appendChild(names[i].toSaveXML(doc, "Name" + i));
		cardElementElt.appendChild(party.toSaveXML(doc));
		return cardElementElt;
	}

	/**
	 * Converts this card element to an XML representation
	 * @param doc the document
	 * @return the element for this ACardElement
	 */
	public Element toXML(Document doc) {
		Element cardElementElt = doc.createElement("SelectableCardElement");
		cardElementElt.setAttribute("uid", uniqueID);
		return cardElementElt;
	}
}
