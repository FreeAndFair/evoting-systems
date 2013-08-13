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
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.util.HashMap;

import javax.swing.BorderFactory;
import javax.swing.JMenuItem;
import javax.swing.JPopupMenu;
import javax.swing.JTextArea;
import javax.swing.SwingUtilities;


import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;

import preptool.model.XMLTools;
import preptool.model.language.Language;
import preptool.model.language.LocalizedString;
import preptool.view.AModuleView;
import preptool.view.View;


/**
 * A TextAreaModule is a module that stores localized text on a card. The view
 * for this module is a large text area for the user to enter a large amount of
 * text.
 * 
 * @author cshaw
 */
public class TextAreaModule extends AModule {

    /**
     * An inner class for the TextAreaModule's view
     * 
     * @author cshaw
     */
    private class ModuleView extends AModuleView {

        private static final long serialVersionUID = 1L;

        private JTextArea field;

        private Language primaryLanguage;

        private Language language;

        private JMenuItem copyFromItem;

        /**
         * Constructs a new ModuleView with the given main view
         * 
         * @param view
         */
        protected ModuleView(View view) {
            setLayout( new GridBagLayout() );
            GridBagConstraints c = new GridBagConstraints();

            field = new JTextArea( getData( language ) );
            field.setBorder( BorderFactory.createTitledBorder( label ) );
            field.addKeyListener( new KeyAdapter() {
                @Override
                public void keyTyped(KeyEvent e) {
                    SwingUtilities.invokeLater( new Runnable() {
                        public void run() {
                            setData( language, field.getText() );
                        }
                    } );
                }
            } );
            JPopupMenu contextMenu = new JPopupMenu();
            copyFromItem = new JMenuItem();
            copyFromItem.addActionListener( new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    setData( language, getData( primaryLanguage ) );
                    field.setText( getData( language ) );
                }
            } );
            contextMenu.add( copyFromItem );
            field.setComponentPopupMenu( contextMenu );
            c.gridx = 0;
            c.weightx = 1;
            c.weighty = 1;
            c.insets = new Insets( 0, 0, 0, 0 );
            c.fill = GridBagConstraints.BOTH;
            add( field, c );
        }

        /**
         * Updates the language to the new selected language
         */
        public void languageSelected(Language lang) {
            language = lang;
            field.setText( getData( lang ) );
        }

        /**
         * Returns true if the module needs to be translated in the given
         * language
         */
        public boolean needsTranslation(Language lang) {
            return TextAreaModule.this.needsTranslation( lang );
        }

        /**
         * Updates the primary language
         */
        public void updatePrimaryLanguage(Language lang) {
            primaryLanguage = lang;
            copyFromItem.setText( "Copy from " + lang.getName() );
        }
    }

    /**
     * Parses an XML Element into a TextAreaModule
     * 
     * @param elt
     *            the element
     * @return the TextAreaModule
     */
    public static TextAreaModule parseXML(Element elt) {
        assert elt.getTagName().equals( "Module" );
        assert elt.getAttribute( "type" ).equals( "TextAreaModule" );

        HashMap<String, Object> properties = XMLTools.getProperties( elt );

        String name = elt.getAttribute( "name" );
        String label = (String) properties.get( "label" );

        TextAreaModule module = new TextAreaModule( name, label );

        NodeList list = elt.getElementsByTagName( "LocalizedString" );
        for (int i = 0; i < list.getLength(); i++) {
            Element child = (Element) list.item( i );
            if (child.getAttribute( "name" ).equals( "Data" ))
                module.data = LocalizedString.parseXML( child );
        }

        return module;
    }

    private LocalizedString data;

    private String label;

    /**
     * Constructs a new TextAreaModule with given module name and label
     * 
     * @param name
     *            the module name
     * @param label
     *            the label to be shown next to the text area on the view
     */
    public TextAreaModule(String name, String label) {
        super( name );
        this.label = label;
        data = new LocalizedString();
    }

    /**
     * Generates ane returns the view for this module
     */
    @Override
    public AModuleView generateView(View view) {
        return new ModuleView( view );
    }

    /**
     * Returns the data as a String in the given language
     * 
     * @param lang
     *            the language
     */
    public String getData(Language lang) {
        return data.get( lang );
    }

    /**
     * Returns true if the module needs to be translated in the given language
     */
    @Override
    public boolean needsTranslation(Language lang) {
        return getData( lang ).equals( "" );
    }

    /**
     * Sets the data to the given string
     * 
     * @param lang
     *            the language
     * @param s
     *            the string
     */
    public void setData(Language lang, String s) {
        data.set( lang, s );
        setChanged();
        notifyObservers();
    }

    /**
     * Formats this TextAreaModule as a savable XML Element
     */
    @Override
    public Element toSaveXML(Document doc) {
        Element moduleElt = doc.createElement( "Module" );
        moduleElt.setAttribute( "type", "TextAreaModule" );
        moduleElt.setAttribute( "name", getName() );

        XMLTools.addProperty( doc, moduleElt, "label", "String", label );

        moduleElt.appendChild( data.toSaveXML( doc, "Data" ) );

        return moduleElt;
    }

}
