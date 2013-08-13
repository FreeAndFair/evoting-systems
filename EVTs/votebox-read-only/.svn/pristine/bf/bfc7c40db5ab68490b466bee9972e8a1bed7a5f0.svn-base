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

import javax.swing.AbstractAction;
import javax.swing.BorderFactory;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JMenuItem;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JPopupMenu;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.JToolBar;
import javax.swing.ListSelectionModel;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;
import javax.swing.event.TableModelEvent;
import javax.swing.event.TableModelListener;

import preptool.model.Party;
import preptool.model.language.Language;
import preptool.view.IMovableTableModel;
import preptool.view.IMultiLanguageEditor;
import preptool.view.LanguageBar;
import preptool.view.MovableTableModel;
import preptool.view.View;
import preptool.view.dragndrop.TableTransferHandler;


/**
 * A Dialog that allows the user to edit the parties that are used in the
 * ballot.
 * 
 * @author cshaw
 */
public class PartiesDialog extends JDialog implements IMultiLanguageEditor {

    private static final long serialVersionUID = 1L;

    /**
     * The list of parties
     */
    private ArrayList<Party> parties;

    /**
     * Table model of the parties table
     */
    private MovableTableModel partiesTableModel;

    /**
     * Table to edit the parties
     */
    private JTable partiesTable;

    /**
     * Table model listener
     */
    private TableModelListener tableListener;

    /**
     * Panel that contains the parties table and toolbar
     */
    private JPanel partiesPanel;

    /**
     * Button to add a party
     */
    private JButton addButton;

    /**
     * Button to remove a party
     */
    private JButton deleteButton;

    /**
     * Toolbar for the add/remove buttons
     */
    private JToolBar partiesToolbar;

    /**
     * An OK button
     */
    private JButton okButton;

    /**
     * Panel containing the OK and cancel buttons
     */
    private JPanel buttonPanel;

    /**
     * Whether the OK button was pressed to close this dialog
     */
    private boolean okButtonWasPressed;

    /**
     * Language bar
     */
    private LanguageBar languageBar;

    /**
     * Menu item to copy a candidate from the primary language
     */
    private JMenuItem tableCopyFromItem;

    /**
     * Menu item to copy all candidates from the primary language
     */
    private JMenuItem tableCopyAllFromItem;

    /**
     * Constructs a new PartiesDialog
     * 
     * @param view
     *            the view
     * @param parties
     *            the parties
     * @param languages
     *            the languages
     * @param startLang
     *            the initial language
     */
    public PartiesDialog(View view, ArrayList<Party> parties,
            ArrayList<Language> languages, Language startLang) {
        super( view, "Parties", true );
        this.parties = parties;

        setSize( 400, 400 );
        setLocationRelativeTo( view );
        setLayout( new GridBagLayout() );
        GridBagConstraints c = new GridBagConstraints();

        JLabel titleLabel = new JLabel( "Edit Parties:" );
        c.gridx = 0;
        c.gridy = 0;
        c.insets = new Insets( 15, 15, 0, 15 );
        c.weightx = 1;
        add( titleLabel, c );

        initializeTablePane( startLang );
        c.gridy = 1;
        c.weighty = 1;
        c.anchor = GridBagConstraints.FIRST_LINE_START;
        c.fill = GridBagConstraints.BOTH;
        add( partiesPanel, c );

        initializeButtons();
        c.gridy = 2;
        c.insets = new Insets( 15, 15, 15, 15 );
        c.weighty = 0;
        c.fill = GridBagConstraints.NONE;
        c.anchor = GridBagConstraints.PAGE_END;
        add( buttonPanel, c );

        languageBar = new LanguageBar( view, this, languages, startLang );
        languageBar.refreshEditorLanguage();
        c.gridy = 3;
        c.insets = new Insets( 0, 0, 0, 0 );
        c.fill = GridBagConstraints.HORIZONTAL;
        c.anchor = GridBagConstraints.LINE_START;
        add( languageBar, c );
    }

    /**
     * Initializes the OK button
     */
    private void initializeButtons() {
        buttonPanel = new JPanel();

        okButton = new JButton( "OK" );
        okButton.addActionListener( new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                okButtonWasPressed = true;
                setVisible( false );
            }
        } );
        buttonPanel.add( okButton );
    }

    /**
     * Initializes the table panel
     */
    private void initializeTablePane(Language lang) {
        partiesPanel = new JPanel();
        partiesPanel.setLayout( new GridBagLayout() );
        GridBagConstraints c = new GridBagConstraints();

        tableListener = new TableModelListener() {
            public void tableChanged(TableModelEvent e) {
                if (e.getType() == IMovableTableModel.MOVE) {
                    Party p = parties.remove( e.getFirstRow() );
                    parties.add( e.getLastRow(), p );
                }
                else {
                    for (int i = e.getFirstRow(); i <= e.getLastRow(); i++) {
                        if (e.getType() == TableModelEvent.INSERT)
                            parties.add( i, new Party() );
                        else if (e.getType() == TableModelEvent.UPDATE) {
                            Party p = parties.get( i );
                            String str = (String) partiesTableModel.getValueAt(
                                i, 0 );
                            if (str != null)
                                p.setName( languageBar.getCurrentLanguage(),
                                    str );
                            else
                                p
                                        .setName( languageBar
                                                .getCurrentLanguage(), "" );
                            str = (String) partiesTableModel.getValueAt( i, 1 );
                            if (str != null)
                                p.setAbbrev( languageBar.getCurrentLanguage(),
                                    str );
                            else
                                p.setAbbrev( languageBar.getCurrentLanguage(),
                                    "" );
                        }
                        else if (e.getType() == TableModelEvent.DELETE)
                            parties.remove( i );
                    }
                }
            }
        };
        partiesTableModel = new MovableTableModel( new String[] {
                "Name", "Abbreviation"
        }, parties.size() );
        partiesTableModel.addTableModelListener( tableListener );
        languageSelected( lang );
        partiesTable = new JTable( partiesTableModel );
        partiesTable.setDragEnabled( true );
        partiesTable.setTransferHandler( new TableTransferHandler() );
        partiesTable.getSelectionModel().setSelectionMode(
            ListSelectionModel.SINGLE_SELECTION );
        partiesTable.getSelectionModel().addListSelectionListener(
            new ListSelectionListener() {
                public void valueChanged(ListSelectionEvent e) {
                    if (partiesTable.getSelectedRow() == -1) {
                        deleteButton.setEnabled( false );
                    }
                    else {
                        deleteButton.setEnabled( true );
                    }
                }
            } );
        JPopupMenu tableContextMenu = new JPopupMenu();
        tableCopyFromItem = new JMenuItem();
        tableCopyFromItem.addActionListener( new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                if (partiesTable.getSelectedRow() != -1) {
                    Party p = parties.get( partiesTable.getSelectedRow() );
                    p.setName( languageBar.getCurrentLanguage(), p
                            .getName( languageBar.getPrimaryLanguage() ) );
                    p.setAbbrev( languageBar.getCurrentLanguage(), p
                            .getAbbrev( languageBar.getPrimaryLanguage() ) );
                    languageSelected( languageBar.getCurrentLanguage() );
                }
            }
        } );
        tableContextMenu.add( tableCopyFromItem );
        tableCopyAllFromItem = new JMenuItem();
        tableCopyAllFromItem.addActionListener( new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                for (Party p : parties) {
                    p.setName( languageBar.getCurrentLanguage(), p
                            .getName( languageBar.getPrimaryLanguage() ) );
                    p.setAbbrev( languageBar.getCurrentLanguage(), p
                            .getAbbrev( languageBar.getPrimaryLanguage() ) );
                }
                languageSelected( languageBar.getCurrentLanguage() );
            }
        } );
        tableContextMenu.add( tableCopyAllFromItem );
        partiesTable.setComponentPopupMenu( tableContextMenu );

        JScrollPane tableScrollPane = new JScrollPane( partiesTable );
        c.gridx = 0;
        c.gridy = 0;
        c.fill = GridBagConstraints.BOTH;
        c.weighty = 1;
        c.weightx = 1;
        partiesPanel.add( tableScrollPane, c );

        partiesToolbar = new JToolBar();
        partiesToolbar.setFloatable( false );

        ImageIcon icon;
        String text;

        try {
            icon = new ImageIcon( ClassLoader.getSystemClassLoader()
                    .getResource( "images/list-add.png" ) );
            text = "";
        }
        catch (Exception e) {
            icon = null;
            text = "Add";
        }
        addButton = new JButton( new AbstractAction( text, icon ) {
            private static final long serialVersionUID = 1L;

            public void actionPerformed(ActionEvent e) {
                addButtonPressed();
            }
        } );
        partiesToolbar.add( addButton );

        try {
            icon = new ImageIcon( ClassLoader.getSystemClassLoader()
                    .getResource( "images/list-remove.png" ) );
            text = "";
        }
        catch (Exception e) {
            icon = null;
            text = "Remove";
        }
        deleteButton = new JButton( new AbstractAction( text, icon ) {
            private static final long serialVersionUID = 1L;

            public void actionPerformed(ActionEvent e) {
                deleteButtonPressed();
            }
        } );
        deleteButton.setEnabled( false );
        partiesToolbar.add( deleteButton );

        c.gridy = 1;
        c.weighty = 0;
        c.anchor = GridBagConstraints.LAST_LINE_START;
        partiesPanel.add( partiesToolbar, c );

        partiesPanel.setBorder( BorderFactory.createTitledBorder( "Parties" ) );
    }

    /**
     * Adds a new row to the end of the table
     */
    public void addButtonPressed() {
        partiesTableModel.addRow( new String[2] );
    }

    /**
     * Deletes the selected row from this table
     */
    public void deleteButtonPressed() {
        if (partiesTable.getEditingRow() == -1) {
            int answer = JOptionPane.showConfirmDialog( this,
                "Are you sure you want to delete this party?", "Delete Party",
                JOptionPane.YES_NO_OPTION );
            if (answer == JOptionPane.YES_OPTION) {
                int idx = partiesTable.getSelectedRow();
                if (partiesTableModel.getRowCount() > 1) {
                    int newIdx;
                    if (idx == partiesTableModel.getRowCount() - 1)
                        newIdx = idx - 1;
                    else
                        newIdx = idx + 1;
                    partiesTable.clearSelection();
                    partiesTable.addRowSelectionInterval( newIdx, newIdx );
                }
                partiesTableModel.removeRow( idx );
            }
        }
    }

    /**
     * @return the okButtonWasPressed
     */
    public boolean okButtonWasPressed() {
        return okButtonWasPressed;
    }

    /**
     * Updates this dialog to show the selected language
     */
    public void languageSelected(Language lang) {
        partiesTableModel.removeTableModelListener( tableListener );
        for (int i = 0; i < parties.size(); i++) {
            partiesTableModel.setValueAt( parties.get( i ).getName( lang ), i,
                0 );
            partiesTableModel.setValueAt( parties.get( i ).getAbbrev( lang ),
                i, 1 );
        }
        partiesTableModel.addTableModelListener( tableListener );
    }

    /**
     * Returns true if there are missing translations in the list of parties
     */
    public boolean needsTranslation(Language lang) {
        for (int i = 0; i < parties.size(); i++)
            if (parties.get( i ).getAbbrev( lang ).equals( "" )
                    || parties.get( i ).getName( lang ).equals( "" ))
                return true;
        return false;
    }

    /**
     * Called when the primary language has changed
     */
    public void updatePrimaryLanguage(Language lang) {
        tableCopyFromItem
                .setText( "Copy selected party from " + lang.getName() );
        tableCopyAllFromItem
                .setText( "Copy all parties from " + lang.getName() );
    }

}
