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

package preptool.model;


import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;

import preptool.model.language.Language;
import preptool.model.language.LocalizedString;

/**
 * Encapsulates a party's localized name and abbreviation.
 * @author cshaw
 */
public class Party {

	/**
	 * A blank party, signifies a candidate without a party
	 */
	public static Party NO_PARTY = new Party();

	/**
	 * The name of the party
	 */
	private LocalizedString name;

	/**
	 * The abbreviation
	 */
	private LocalizedString abbrev;

	/**
	 * Constructs a new Party.
	 */
	public Party() {
		name = new LocalizedString();
		abbrev = new LocalizedString();
	}

	/**
	 * Clears the party so it is identical to NO_PARTY - used when deleting a
	 * party
	 */
	public void clear() {
		name = new LocalizedString();
		abbrev = new LocalizedString();
	}

	/**
	 * Checks the name and abbreviation localized strings
	 */
	@Override
	public boolean equals(Object obj) {
		if (!(obj instanceof Party)) return false;
		Party rhs = (Party) obj;
		return name.equals(rhs.name) && abbrev.equals(rhs.abbrev);
	}

	/**
	 * @return the abbrev
	 */
	public String getAbbrev(Language lang) {
		return abbrev.get(lang);
	}

	/**
	 * @return the name
	 */
	public String getName(Language lang) {
		return name.get(lang);
	}

	/**
	 * @param lang the language of this abbreviation
	 * @param abbrev the abbreviation to set
	 */
	public void setAbbrev(Language lang, String abbrev) {
		this.abbrev.set(lang, abbrev);
	}

	/**
	 * @param abbrev the abbreviation to set
	 */
	public void setAbbrev(LocalizedString abbrev) {
		this.abbrev = abbrev;
	}

	/**
	 * @param lang the language this name is in
	 * @param name the name to set
	 */
	public void setName(Language lang, String name) {
		this.name.set(lang, name);
	}

	/**
	 * @param name the name to set
	 */
	public void setName(LocalizedString name) {
		this.name = name;
	}

	/**
	 * Converts this party to a savable XML representation, to be opened later
	 * @param doc the document
	 * @return the element for this Party
	 */
	public Element toSaveXML(Document doc) {
		Element elt = doc.createElement("Party");
		elt.appendChild(name.toSaveXML(doc, "Name"));
		elt.appendChild(abbrev.toSaveXML(doc, "Abbrev"));
		return elt;
	}

	/**
	 * Parses XML into a Party object
	 * @param elt the element
	 * @return the Party
	 */
	public static Party parseXML(Element elt) {
		assert elt.getTagName().equals("Party");
		Party party = new Party();

		NodeList list = elt.getElementsByTagName("LocalizedString");
		for (int i = 0; i < list.getLength(); i++) {
			Element child = (Element) list.item(i);
			if (child.getAttribute("name").equals("Name"))
				party.setName(LocalizedString.parseXML(child));
			if (child.getAttribute("name").equals("Abbrev"))
				party.setAbbrev(LocalizedString.parseXML(child));
		}

		return party;
	}

}
