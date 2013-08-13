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

package supervisor.view;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.util.Observable;
import java.util.Observer;

import javax.swing.BorderFactory;
import javax.swing.JLabel;
import javax.swing.border.BevelBorder;

import supervisor.model.SupervisorMachine;

/**
 * The view for a supervisor on the network.
 * @author cshaw
 */
@SuppressWarnings("serial")
public class SupervisorMachineView extends AMachineView {

    private SupervisorMachine machine;

    private JLabel supervisorLabel;

    private JLabel serialLabel;

    private JLabel statusLabel;

    private JLabel currentLabel;

    /**
     * Constructs a new SupervisorMachineView
     * @param mach the supervisor machine model
     */
    public SupervisorMachineView(SupervisorMachine mach) {
        machine = mach;
        setLayout(new GridBagLayout());
        GridBagConstraints c = new GridBagConstraints();

        supervisorLabel = new MyJLabel("Supervisor");
        supervisorLabel.setFont(supervisorLabel.getFont().deriveFont(Font.BOLD,
                16f));
        c.gridy = 0;
        c.weighty = 1;
        c.anchor = GridBagConstraints.PAGE_END;
        add(supervisorLabel, c);

        serialLabel = new MyJLabel("#" + mach.getSerial());
        c.gridy = 1;
        c.weighty = 0;
        c.insets = new Insets(0, 0, 10, 0);
        add(serialLabel, c);

        statusLabel = new MyJLabel();
        statusLabel.setFont(statusLabel.getFont().deriveFont(Font.BOLD, 14f));
        c.gridy = 2;
        c.insets = new Insets(0, 0, 0, 0);
        add(statusLabel, c);

        currentLabel = new MyJLabel();
        c.gridy = 3;
        c.weighty = 1;
        c.anchor = GridBagConstraints.PAGE_START;
        add(currentLabel, c);

        setBorder(BorderFactory.createBevelBorder(BevelBorder.RAISED));
        setSize(180, 160);
        setMinimumSize(new Dimension(180, 175));
        setPreferredSize(new Dimension(180, 175));
        setMaximumSize(new Dimension(180, 175));

        machine.addObserver(new Observer() {
            public void update(Observable o, Object arg) {
                updateView();
            }
        });

        updateView();
    }

    /**
     * Queries information from the supervisor machine's model, and updates the
     * view accordingly. Also called whenever the observer is notified.
     */
    public void updateView() {
        if (machine.isOnline()) {
            updateBackground(Color.CYAN);
            if (machine.getStatus() == SupervisorMachine.ACTIVE)
                statusLabel.setText("Active");
            else
                statusLabel.setText("Inactive");
        } else {
            updateBackground(Color.LIGHT_GRAY);
            statusLabel.setText("Offline");
        }
        if (machine.isCurrentMachine())
            currentLabel.setText("(Current Machine)");
        else
            currentLabel.setText("");
        revalidate();
        repaint();
    }

    /**
     * Updates the background to a given color
     * @param c the color
     */
    private void updateBackground(Color c) {
        setBackground(c);
    }

}
