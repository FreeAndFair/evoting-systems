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

import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.SwingUtilities;

public class ExceptionDialog extends JDialog {

    private static final long serialVersionUID = 1L;

    /**
     * The title label on the dialog
     */
    private JLabel titleLabel;

    /**
     * The sub task label on the dialog
     */
    private JTextArea textArea;

    /**
     * The OK button on the dialog
     */
    private JButton okButton;

    /**
     * Constructs a new ProgressTask with the given parent frame and title
     * 
     * @param parent
     *            the parent frame
     * @param stackTrace
     *            the exception's stack trace
     */
    public ExceptionDialog(JFrame parent, String message,
            StackTraceElement[] stackTrace) {
        super( parent, "Unhandled Exception", true );
        this.setSize( 700, 500 );
        this.setLocationRelativeTo( parent );
        this.setLayout( new GridBagLayout() );
        GridBagConstraints c = new GridBagConstraints();

        titleLabel = new JLabel( message );
        c.gridx = 0;
        c.gridy = 0;
        c.insets = new Insets( 15, 15, 15, 15 );
        c.weightx = 1;
        c.anchor = GridBagConstraints.FIRST_LINE_START;
        c.fill = GridBagConstraints.BOTH;
        this.add( titleLabel, c );

        String stackTraceString = "";
        for (StackTraceElement s : stackTrace)
            stackTraceString += s + "\n";

        textArea = new JTextArea();
        textArea.setText( stackTraceString );
        c.gridy = 1;
        c.insets = new Insets( 0, 15, 15, 15 );
        c.weighty = 1;
        JScrollPane textAreaScrollPane = new JScrollPane( textArea );
        textAreaScrollPane.setBorder( BorderFactory
                .createTitledBorder( "Stack Trace:" ) );
        this.add( textAreaScrollPane, c );

        JPanel buttonPanel = new JPanel();
        okButton = new JButton( "OK" );
        okButton.addActionListener( new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                setVisible( false );
            }
        } );
        buttonPanel.add( okButton );

        c.gridy = 2;
        c.insets = new Insets( 0, 15, 15, 15 );
        c.weighty = 0;
        c.fill = GridBagConstraints.NONE;
        c.anchor = GridBagConstraints.PAGE_END;
        this.add( buttonPanel, c );
    }

    /**
     * Shows the dialog.
     */
    public void showDialog() {
        SwingUtilities.invokeLater( new Runnable() {
            public void run() {
                setVisible( true );
            }
        } );
    }

}
