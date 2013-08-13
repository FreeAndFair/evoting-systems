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

package preptool.model.ballot.module;

import java.util.Observable;


import org.w3c.dom.Document;
import org.w3c.dom.Element;

import preptool.controller.exception.BallotOpenException;
import preptool.model.language.Language;
import preptool.view.AModuleView;
import preptool.view.View;


/**
 * A Module is a component of an ACard that holds some data and (usually) has an editor
 * view associated with it.  Adding new information to cards is as simple as adding the
 * Module corresponding to that type of information.
 * @author cshaw
 */
public abstract class AModule extends Observable {

    /**
     * Parses an XML Element into a module
     * @param elt the element
     * @return the AModule
     */
    public static AModule parseXML(Element elt) {
        assert elt.getTagName().equals("Module");
        String type = elt.getAttribute("type");
        if (type.equals("CandidatesModule"))
            return CandidatesModule.parseXML(elt);
        else if (type.equals("CheckBoxModule"))
            return CheckBoxModule.parseXML(elt);
        else if (type.equals("TextAreaModule"))
            return TextAreaModule.parseXML(elt);
        else if (type.equals("TextFieldModule"))
            return TextFieldModule.parseXML(elt);
        else if (type.equals("YesNoOptionsModule"))
            return YesNoOptionsModule.parseXML(elt);
        else
            throw new BallotOpenException("Invalid module: " + type);
    }

    private String name;

    /**
     * Creates a new Module with the given unique name
     * @param name the name of the module
     */
    public AModule(String name) {
        this.name = name;
    }
    
    /**
     * Abstract method for generating the view of this module
     * @param view the main view
     * @return an AModuleView for this module
     */
    public abstract AModuleView generateView(View view);

    /**
     * Returns this module's name.  The name is a unique identifier of this module that the
     * ACard (or user of the card) can use to access this module. 
     */
    public String getName() {
        return name;
    }

    /**
     * Returns true if this module has an editor view, defaults to true
     * @return true
     */
    public boolean hasView() {
        return true;
    }

    /**
     * Checks whether the information in this module is missing any translations
     * @param lang the language to check
     * @return true if missing translation information
     */
    public abstract boolean needsTranslation(Language lang);

    /**
     * Formats this module as a savable XML Element
     * @param doc the document
     * @return the Element
     */
    public abstract Element toSaveXML(Document doc);

}
