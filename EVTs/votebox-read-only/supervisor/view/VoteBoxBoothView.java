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

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.IOException;
import java.net.URL;
import java.util.Observable;
import java.util.Observer;

import javax.swing.BorderFactory;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.border.BevelBorder;

import supervisor.model.Model;
import supervisor.model.VoteBoxBooth;

/**
 * The view of a VoteBox booth on the network. Shows information such as the
 * label, status, battery level, and public/protected counts. It also has a
 * button for authorization or override. The button is hidden when the polls are
 * closed.
 * @author cshaw
 */
@SuppressWarnings("serial")
public class VoteBoxBoothView extends AMachineView {

    private Model model;

    private ActiveUI view;

    private VoteBoxBooth machine;

    private JLabel nameLabel;

    private JLabel serialLabel;

    private JLabel batteryLabel;

    private JLabel statusLabel;

    private JLabel publicCountLabel;

    private JLabel protectedCountLabel;

    private JButton button;

    private JPanel buttonPanel;

    private JPanel statusPanel;

    private JPanel namePanel;

    /**
     * Constructs a new VoteBoxBoothView.
     * @param m the model
     * @param v the active UI
     * @param mach the booth's model
     */
    public VoteBoxBoothView(Model m, ActiveUI v, VoteBoxBooth mach) {
        model = m;
        view = v;
        machine = mach;
        GridBagConstraints c = new GridBagConstraints();

        nameLabel = new MyJLabel();
        nameLabel.setFont(nameLabel.getFont().deriveFont(Font.BOLD, 24));
        serialLabel = new MyJLabel();
        serialLabel.setFont(serialLabel.getFont().deriveFont(9f));
        namePanel = new JPanel();
        namePanel.setLayout(new GridBagLayout());
        c.weighty = .8;
        c.anchor = GridBagConstraints.PAGE_END;
        namePanel.add(nameLabel, c);
        c.weighty = 1;
        c.gridy = 1;
        c.anchor = GridBagConstraints.CENTER;
        namePanel.add(serialLabel, c);
        namePanel.setBorder(BorderFactory.createMatteBorder(0, 0, 1, 1,
                Color.BLACK));

        c = new GridBagConstraints();

        batteryLabel = new JLabel();
        batteryLabel.setVisible(false);

        statusLabel = new MyJLabel();
        statusLabel.setFont(statusLabel.getFont().deriveFont(Font.BOLD));
        publicCountLabel = new MyJLabel();
        publicCountLabel.setFont(publicCountLabel.getFont().deriveFont(9f));
        protectedCountLabel = new MyJLabel();
        protectedCountLabel.setFont(protectedCountLabel.getFont()
                .deriveFont(9f));
        statusPanel = new JPanel();
        statusPanel.setLayout(new GridBagLayout());
        c.weighty = 1;
        c.anchor = GridBagConstraints.CENTER;
        c.insets = new Insets(5, 0, 5, 0);
        statusPanel.add(batteryLabel, c);
        c.gridy = 1;
        c.weighty = 1;
        c.insets = new Insets(0, 0, 0, 0);
        statusPanel.add(statusLabel, c);
        c.anchor = GridBagConstraints.PAGE_START;
        c.gridy = 2;
        c.weighty = 0;
        statusPanel.add(publicCountLabel, c);
        c.gridy = 3;
        c.weighty = 1;
        statusPanel.add(protectedCountLabel, c);
        statusPanel.setBorder(BorderFactory.createMatteBorder(0, 0, 1, 0,
                Color.BLACK));
        statusPanel.setPreferredSize(new Dimension(70, 70));

        c = new GridBagConstraints();
        button = new MyJButton();
        button.setLayout(new GridBagLayout());
        button.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                buttonPressed();
            }
        });
        button.setVisible(model.isPollsOpen());
        buttonPanel = new JPanel();
        buttonPanel.setLayout(new BorderLayout());
        buttonPanel.add(button, BorderLayout.CENTER);

        setLayout(new GridBagLayout());

        c.gridx = 0;
        c.gridy = 0;
        c.weightx = 1;
        c.weighty = 0;
        c.anchor = GridBagConstraints.CENTER;
        c.fill = GridBagConstraints.BOTH;
        add(namePanel, c);

        c.gridx = 1;
        add(statusPanel, c);

        c.gridx = 0;
        c.gridy = 1;
        c.gridwidth = 2;
        c.weighty = 1;
        c.insets = new Insets(8, 8, 8, 8);
        add(buttonPanel, c);

        // setBorder(BorderFactory.createLineBorder(Color.BLACK, 1));
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
     * Updates the background to a given color
     * @param c the color
     */
    public void updateBackground(Color c) {
        setBackground(c);
        namePanel.setBackground(c);
        statusPanel.setBackground(c);
        buttonPanel.setBackground(c);
    }

    /**
     * Queries information from the VoteBox booth's model, and updates the view
     * accordingly. Also called whenever the observer is notified.
     */
    public void updateView() {
        nameLabel.setText(Integer.toString(machine.getLabel()));
        serialLabel.setText("#" + machine.getSerial());
        GridBagConstraints c = new GridBagConstraints();

        VoteBoxBooth m = (VoteBoxBooth) machine;

        if (machine.isOnline()) {
            publicCountLabel.setVisible(true);
            protectedCountLabel.setVisible(true);
            publicCountLabel.setText("Public Count: " + m.getPublicCount());
            protectedCountLabel.setText("Protected Count: "
                    + m.getProtectedCount());
            button.setVisible(model.isPollsOpen());
            button.removeAll();
            button.setEnabled(true);
            if (machine.getStatus() == VoteBoxBooth.READY) {
                updateBackground(Color.WHITE);
                statusLabel.setText("Ready");
                button.add(new MyJLabel("Authorize"), c);
                c.gridy = 1;
                button.add(new MyJLabel("Voter"), c);
            } else if (machine.getStatus() == VoteBoxBooth.IN_USE) {
                updateBackground(Color.YELLOW);
                statusLabel.setText("In Use");
                button.add(new MyJLabel("Override"), c);
            }

            batteryLabel.setVisible(true);
            String batteryIcon = "images/batt" + ((m.getBattery() + 10) / 20)
                    + ".png";

            URL url = ClassLoader.getSystemClassLoader().getResource(
                    batteryIcon);
            if (url != null) batteryLabel.setIcon(new ImageIcon(url));

        } else {
            updateBackground(Color.LIGHT_GRAY);
            batteryLabel.setVisible(false);
            publicCountLabel.setVisible(false);
            protectedCountLabel.setVisible(false);
            statusLabel.setText("Offline");
            button.setVisible(false);
        }
        revalidate();
        repaint();
    }

    /**
     * Called whenever the main button on the view is pressed, and determines
     * whether this means to authorize, or override, that machine.
     */
    private void buttonPressed() {
        if (machine.isOnline()) {
            if (machine.getStatus() == VoteBoxBooth.READY) {
                try {
                    button.setEnabled(false);
                    button.removeAll();
                    button.add(new MyJLabel("Waiting"));
                    repaint();
                    model.authorize(machine.getSerial());
                } catch (IOException e) {
                    System.err.println("Error encountered while authorizing <"+e.getMessage()+">");
                    e.printStackTrace();
                }
            } else {
                JDialog dlg = new OverrideDialog(view, model, machine
                        .getSerial(), machine.getLabel());
                dlg.setVisible(true);
            }
        }
    }

}
