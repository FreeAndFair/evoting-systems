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

import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.HashMap;

import javax.swing.JCheckBox;
import javax.swing.JLabel;


import org.w3c.dom.Document;
import org.w3c.dom.Element;

import preptool.model.XMLTools;
import preptool.model.language.Language;
import preptool.view.AModuleView;
import preptool.view.View;


/**
 * A CheckBoxModule is a module that allows the user to specify a togglable
 * option on a card. The view for this module is a check box with a label.
 * 
 * @author cshaw
 */
public class CheckBoxModule extends AModule {

    /**
     * An inner class for the CheckBoxModule's view
     * 
     * @author cshaw
     */
    private class ModuleView extends AModuleView {

        private static final long serialVersionUID = 1L;
        private JCheckBox checkBox;

        /**
         * Constructs the module view
         * 
         * @param view
         *            the main view
         */
        protected ModuleView(View view) {
            setLayout( new GridBagLayout() );
            GridBagConstraints c = new GridBagConstraints();

            c.gridx = 0;
            c.gridy = 0;
            c.anchor = GridBagConstraints.LINE_START;
            JLabel prompt = new JLabel( label + ":  " );
            add( prompt, c );

            checkBox = new JCheckBox();
            checkBox.addActionListener( new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    setData( checkBox.isSelected() );
                }
            } );
            c.gridx = 1;
            c.weightx = 1;
            add( checkBox, c );
        }

        /**
         * Does nothing
         */
        public void languageSelected(Language lang) {
        // NO-OP
        }

        /**
         * @return false
         */
        public boolean needsTranslation(Language lang) {
            return false;
        }

        /**
         * Does nothing
         */
        public void updatePrimaryLanguage(Language lang) {
        // NO-OP
        }
    }

    /**
     * Parses this XML Element into a CheckBoxModule
     * 
     * @param elt
     *            the Element
     * @return the CheckBoxModule
     */
    public static CheckBoxModule parseXML(Element elt) {
        assert elt.getTagName().equals( "Module" );
        assert elt.getAttribute( "type" ).equals( "CheckBoxModule" );

        HashMap<String, Object> properties = XMLTools.getProperties( elt );

        String name = elt.getAttribute( "name" );
        String label = (String) properties.get( "label" );
        boolean data = (Boolean) properties.get( "data" );

        CheckBoxModule module = new CheckBoxModule( name, label, data );

        return module;
    }

    private boolean data;

    private String label;

    /**
     * Constructs a new CheckBoxModule with the given module name and label. The
     * state defaults to false.
     * 
     * @param name
     *            the module name
     * @param label
     *            the label to be shown next to the check box on the view
     */
    public CheckBoxModule(String name, String label) {
        super( name );
        this.label = label;
        data = false;
    }

    /**
     * Constructs a new CheckBoxModule with the given module name, label, and
     * initial state
     * 
     * @param name
     *            the module name
     * @param label
     *            the label to be shown next to the check box on the view
     * @param initial
     *            the initial state
     */
    public CheckBoxModule(String name, String label, boolean initial) {
        this( name, label );
        data = initial;
    }

    /**
     * Generates and returns the view for this module
     */
    @Override
    public AModuleView generateView(View view) {
        return new ModuleView( view );
    }

    /**
     * Returns the data as a boolean
     */
    public boolean getData() {
        return data;
    }

    /**
     * @return false
     */
    @Override
    public boolean needsTranslation(Language lang) {
        return false;
    }

    /**
     * Sets the data to the given boolean
     * 
     * @param d
     *            the new data
     */
    public void setData(boolean d) {
        data = d;
        setChanged();
        notifyObservers();
    }

    /**
     * Formats this CheckBoxModule as a savable XML Element
     * 
     * @param doc
     *            the document
     * @return the Element
     */
    @Override
    public Element toSaveXML(Document doc) {
        Element moduleElt = doc.createElement( "Module" );
        moduleElt.setAttribute( "type", "CheckBoxModule" );
        moduleElt.setAttribute( "name", getName() );

        XMLTools.addProperty( doc, moduleElt, "label", "String", label );
        XMLTools.addProperty( doc, moduleElt, "data", "Boolean", Boolean
                .toString( data ) );

        return moduleElt;
    }

}
