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

package preptool.view;

import java.awt.Color;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.ArrayList;
import java.util.Observer;

import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JLabel;
import javax.swing.JMenuItem;
import javax.swing.JPanel;
import javax.swing.JPopupMenu;
import javax.swing.Timer;

import preptool.model.Event;
import preptool.model.language.Language;


/**
 * A LanguageBar is a JPanel that shows the user what language he is working on,
 * allows him to switch the language, and also allows the user to edit which
 * languages are available. In addition, the bar can check to see if all
 * translation information has been entered, and show a warning if it hasn't.
 * 
 * @author cshaw
 */
public class LanguageBar extends JPanel implements ActionListener {

    private static final long serialVersionUID = 1L;

    /**
     * The main view of the program, for opening a LanguageDialog
     */
    private View view;

    /**
     * The editor that this bar is linked to
     */
    private IMultiLanguageEditor editor;

    /**
     * An array of languages that are available to edit
     */
    private ArrayList<Language> languages;

    /**
     * The current language that the user is editing
     */
    private Language currentLanguage;

    /**
     * A button that spawns a popup menu for the user to choose a language
     */
    private JButton languageButton;

    /**
     * The menu with all of the languages to choose from and an edit option
     */
    private JPopupMenu languageMenu;

    /**
     * A list of menu items
     */
    private ArrayList<JMenuItem> menuItems;

    /**
     * The edit menu item
     */
    private JMenuItem editItem;

    /**
     * A label that warns the user if translation information is missing
     */
    private JLabel statusLabel;

    /**
     * Event that corresponds to a language being selected
     */
    private Event languageSelected = new Event();

    /**
     * Constructs a new LanguageBar
     * 
     * @param view
     *            the view
     * @param ed
     *            the editor
     * @param langs
     *            the languages
     * @param startLanguage
     *            the starting language
     */
    public LanguageBar(View view, IMultiLanguageEditor ed,
            ArrayList<Language> langs, Language startLanguage) {
        super();
        this.view = view;
        this.editor = ed;
        languages = langs;
        currentLanguage = (startLanguage != null) ? startLanguage : languages
                .get( 0 );

        setBorder( BorderFactory.createEtchedBorder() );
        setLayout( new GridBagLayout() );
        GridBagConstraints c = new GridBagConstraints();

        c.gridx = 0;
        c.gridy = 0;
        c.insets = new Insets( 3, 3, 3, 0 );
        c.anchor = GridBagConstraints.LINE_START;
        add( new JLabel( "Language: " ), c );

        languageButton = new JButton( currentLanguage.getName(),
                currentLanguage.getIcon() );
        languageButton.addActionListener( new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                languageMenu.show( languageButton, 0, -(int) languageMenu
                        .getPreferredSize().getHeight() );
            }
        } );
        c.gridx = 1;
        add( languageButton, c );

        initializePopupMenu();

        statusLabel = new JLabel();
        statusLabel.setForeground( Color.RED );
        c.gridx = 2;
        c.weightx = 1;
        c.insets = new Insets( 3, 10, 3, 0 );
        add( statusLabel, c );

        ActionListener checkTranslationTask = new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                boolean res = false;
                for (Language lang : languages)
                    res |= editor.needsTranslation( lang );
                if (res) {
                    statusLabel.setText( "Missing translation information" );
                }
                else {
                    statusLabel.setText( "" );
                }
            }
        };
        Timer timer = new Timer( 5000, checkTranslationTask );
        timer.setInitialDelay( 100 );
        timer.setRepeats( true );
        timer.start();

        view.addLanguageChangeListener( new LanguageChangeListener() {
            public void languagesChanged(ArrayList<Language> langs) {
                languages = langs;
                if (!languages.contains( currentLanguage )) {
                    currentLanguage = languages.get( 0 );
                    languageButton.setIcon( currentLanguage.getIcon() );
                    languageButton.setText( currentLanguage.getName() );
                    editor.languageSelected( currentLanguage );
                    languageSelected.notifyObservers( currentLanguage );
                }
                editor.updatePrimaryLanguage( languages.get( 0 ) );
                initializePopupMenu();
            }
        } );
    }

    /**
     * Called when the user selects a language from the popup menu<br>
     * Figures out which language was selected, then switches to it. If the user
     * pressed the Edit button, show the Language Dialog.
     */
    public void actionPerformed(ActionEvent e) {
        Language lang = null;
        for (int i = 0; i < languages.size(); i++) {
            if (e.getSource() == menuItems.get( i ))
                lang = languages.get( i );
        }
        if (lang != null && currentLanguage != lang) {
            currentLanguage = lang;
            languageButton.setIcon( currentLanguage.getIcon() );
            languageButton.setText( currentLanguage.getName() );
            editor.languageSelected( lang );
            languageSelected.notifyObservers( currentLanguage );
        }
        else {
            if (e.getSource() == editItem) {
                view.showLanguageDialog();
            }
        }
    }

    /**
     * Updates the editor with the current language
     */
    public void refreshEditorLanguage() {
        editor.updatePrimaryLanguage( languages.get( 0 ) );
        editor.languageSelected( currentLanguage );
    }

    /**
     * Initializes the popup menu
     */
    private void initializePopupMenu() {
        languageMenu = new JPopupMenu();
        menuItems = new ArrayList<JMenuItem>();
        for (int i = 0; i < languages.size(); i++) {
            JMenuItem item = new JMenuItem( languages.get( i ).getName(),
                    languages.get( i ).getIcon() );
            item.addActionListener( this );
            menuItems.add( item );
            languageMenu.add( item );
        }
        languageMenu.addSeparator();
        editItem = new JMenuItem( "Edit..." );
        editItem.addActionListener( this );
        languageMenu.add( editItem );
    }

    /**
     * @return the currentLanguage
     */
    public Language getCurrentLanguage() {
        return currentLanguage;
    }

    /**
     * @return the primary language
     */
    public Language getPrimaryLanguage() {
        return languages.get( 0 );
    }

    /**
     * Adds a language select listener
     */
    public void addLanguageSelectListener(Observer l) {
        languageSelected.addObserver( l );
    }
}
