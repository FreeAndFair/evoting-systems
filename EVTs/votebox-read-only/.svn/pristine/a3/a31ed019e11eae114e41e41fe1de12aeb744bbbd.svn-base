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

package preptool.model.layout;

import java.awt.Dimension;


import org.w3c.dom.Document;
import org.w3c.dom.Element;

import preptool.model.XMLTools;
import preptool.model.language.Language;

/**
 * A LanguageButton is a ToggleButton that specifies a language selection
 * on the ballot, thus it must have a Language.
 * @author cshaw
 */
public class LanguageButton extends ToggleButton {

    Language language;

    /**
     * @param uid
     * @param t
     * @param sizeVisitor
     */
    public LanguageButton(String uid, String t,
            ILayoutComponentVisitor<Object, Dimension> sizeVisitor) {
        super(uid, t, sizeVisitor);
    }

    /**
     * @param uid
     * @param t
     */
    public LanguageButton(String uid, String t) {
        super(uid, t);
    }

    /**
     * @return the language
     */
    public Language getLanguage() {
        return language;
    }

    /**
     * @param language the language to set
     */
    public void setLanguage(Language language) {
        this.language = language;
    }
    
    @Override
    public Element toXML(Document doc) {
        Element buttonElt = super.toXML(doc);
        XMLTools.addProperty(doc, buttonElt, "Language", "String", language.getShortName());
        return buttonElt;
    }

}
