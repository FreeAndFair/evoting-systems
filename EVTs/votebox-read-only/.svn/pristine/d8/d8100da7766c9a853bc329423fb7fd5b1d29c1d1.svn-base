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

package preptool.view.dialog;

import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.ArrayList;

import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.SwingConstants;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

import preptool.model.language.Language;
import preptool.view.View;



/**
 * A Dialog that allows the user to select the languages that are in the ballot.
 * 
 * @author cshaw
 */
public class LanguagesDialog extends JDialog {

    private static final long serialVersionUID = 1L;

    /**
     * The list of languages
     */
    private ArrayList<Language> languages;

    /**
     * The list of selected languages
     */
    private ArrayList<Language> selectedLanguages;

    /**
     * An array of the checkboxes, parallel to languages
     */
    private ArrayList<JCheckBox> checkBoxes;

    /**
     * An OK button
     */
    private JButton okButton;

    /**
     * A cancel button
     */
    private JButton cancelButton;

    /**
     * A scroll pane for the languages
     */
    private JScrollPane languagesScrollPane;

    /**
     * Panel containing the OK and cancel buttons
     */
    private JPanel buttonPanel;

    /**
     * Whether the OK button was pressed to close this dialog
     */
    private boolean okButtonWasPressed;

    /**
     * Constructs a new LanguagesDialog
     * 
     * @param view
     *            the view
     * @param languages
     *            the languages
     * @param selectedLanguages
     *            the currently selected languages
     */
    public LanguagesDialog(View view, ArrayList<Language> languages,
            ArrayList<Language> selectedLanguages) {
        super( view, "Languages", true );
        this.languages = languages;
        this.selectedLanguages = selectedLanguages;

        setSize( 200, 400 );
        setLocationRelativeTo( view );
        setLayout( new GridBagLayout() );
        GridBagConstraints c = new GridBagConstraints();

        JLabel titleLabel = new JLabel( "Select Languages:" );
        c.gridx = 0;
        c.gridy = 0;
        c.insets = new Insets( 15, 15, 0, 15 );
        c.weightx = 1;
        add( titleLabel, c );

        initializeScrollPane();
        c.gridy = 1;
        c.weighty = 1;
        c.anchor = GridBagConstraints.FIRST_LINE_START;
        c.fill = GridBagConstraints.BOTH;
        add( languagesScrollPane, c );

        initializeButtons();
        c.gridy = 2;
        c.insets = new Insets( 15, 15, 15, 15 );
        c.weighty = 0;
        c.fill = GridBagConstraints.NONE;
        c.anchor = GridBagConstraints.PAGE_END;
        add( buttonPanel, c );
    }

    /**
     * Initializes the scroll pane containing the list of languages
     */
    private void initializeScrollPane() {
        JPanel languagesPanel = new JPanel();
        languagesPanel.setLayout( new GridBagLayout() );
        GridBagConstraints c = new GridBagConstraints();
        checkBoxes = new ArrayList<JCheckBox>();

        c.ipadx = 3;
        c.ipady = 3;
        c.fill = GridBagConstraints.HORIZONTAL;
        c.anchor = GridBagConstraints.LINE_START;

        ChangeListener cl = new ChangeListener() {
            public void stateChanged(ChangeEvent e) {
                boolean checked = false;
                for (int i = 0; i < checkBoxes.size(); i++)
                    if (checkBoxes.get( i ).isSelected())
                        checked = true;
                okButton.setEnabled( checked );
            }
        };

        for (int i = 0; i < languages.size(); i++) {
            Language lang = languages.get( i );
            JCheckBox checkBox = new JCheckBox();
            checkBox.setSelected( selectedLanguages.contains( lang ) );
            checkBox.addChangeListener( cl );
            checkBoxes.add( checkBox );
            c.gridx = 0;
            c.gridy = i;
            c.weightx = 0;
            languagesPanel.add( checkBox, c );

            JLabel label = new JLabel( lang.getName(), lang.getIcon(),
                    SwingConstants.LEFT );
            c.gridx = 1;
            c.weightx = 1;
            languagesPanel.add( label, c );
        }
        c.gridy = languages.size();
        c.weighty = 1;
        languagesPanel.add( new JLabel( "" ), c );

        languagesScrollPane = new JScrollPane( languagesPanel );
    }

    /**
     * Initializes the OK and cancel buttons
     */
    private void initializeButtons() {
        buttonPanel = new JPanel();

        okButton = new JButton( "OK" );
        okButton.addActionListener( new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                selectedLanguages = new ArrayList<Language>();
                for (int i = 0; i < languages.size(); i++)
                    if (checkBoxes.get( i ).isSelected())
                        selectedLanguages.add( languages.get( i ) );
                okButtonWasPressed = true;
                setVisible( false );
            }
        } );
        buttonPanel.add( okButton );

        cancelButton = new JButton( "Cancel" );
        cancelButton.addActionListener( new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                okButtonWasPressed = false;
                setVisible( false );
            }
        } );
        buttonPanel.add( cancelButton );
    }

    /**
     * @return the okButtonWasPressed
     */
    public boolean okButtonWasPressed() {
        return okButtonWasPressed;
    }

    /**
     * @return the selectedLanguages
     */
    public ArrayList<Language> getSelectedLanguages() {
        return selectedLanguages;
    }
}
