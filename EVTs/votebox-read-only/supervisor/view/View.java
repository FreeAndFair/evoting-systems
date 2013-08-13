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

import java.util.Observable;
import java.util.Observer;

import javax.swing.JFrame;

import supervisor.model.Model;

/**
 * The Supervisor's view. The common denominator is simply the frame, and the
 * observer that switches views between the active and inactive UI.
 * @author cshaw
 */
@SuppressWarnings("serial")
public class View extends JFrame {

    InactiveUI inactiveUI;

    ActiveUI activeUI;

    /**
     * Constructs a new View
     * @param model the model
     */
    public View(final Model model) {
        super("Supervisor Console");

        setSize(1024, 768);
        setDefaultCloseOperation(EXIT_ON_CLOSE);
        // setUndecorated(true);

        activeUI = new ActiveUI(model);
        inactiveUI = new InactiveUI(model);

        model.registerForActivated(new Observer() {
            public void update(Observable o, Object arg) {
                if (model.isActivated())
                    setContentPane(activeUI);
                else
                    setContentPane(inactiveUI);
                validate();
                repaint();
            }
        });
    }

    /**
     * Shows the inactive UI (called after the keyword has been entered).<br>
     * The view is blank until this is called.
     */
    public void display() {
        setContentPane(inactiveUI);
        validate();
        repaint();
    }

}
