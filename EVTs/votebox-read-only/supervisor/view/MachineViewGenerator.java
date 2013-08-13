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

import java.util.HashMap;

import supervisor.model.AMachine;
import supervisor.model.Model;
import supervisor.model.SupervisorMachine;
import supervisor.model.VoteBoxBooth;

/**
 * The MachineViewGenerator is a sort of "cache" that only allows you to create
 * one instance of a view for a machine's model (assuming that all views are
 * created through the same MVG). This is necessary because the update all
 * machines operation, that is executed whenever a machine joins or leaves,
 * throws out all machines and recreates those that are in the list (this
 * handles adds and removes, in order). However, since those views register
 * observers in their machines' models, they would never be garbage collected.
 * This way, when the update all machines operation throws away a view and then
 * attempts to recreate it, the MVG simply calls update on the existing view,
 * and then returns it.
 * @author cshaw
 */
public class MachineViewGenerator {

    private HashMap<AMachine, AMachineView> views;

    /**
     * Constructs a new MachineViewGenerator
     */
    public MachineViewGenerator() {
        views = new HashMap<AMachine, AMachineView>();
    }

    /**
     * Generates a view for a machine. If the view was already created
     * previously, it is simply returned. Otherwise, it is created and stored
     * for the next time the same view is requested.
     * @param model the model
     * @param view the active UI
     * @param m the machine
     * @return the machine's view
     */
    public AMachineView generateView(Model model, ActiveUI view, AMachine m) {
        AMachineView mv = views.get(m);
        if (mv != null) {
            mv.updateView();
            return mv;
        } else {
            if (m instanceof SupervisorMachine) {
                mv = new SupervisorMachineView((SupervisorMachine) m);
            } else if (m instanceof VoteBoxBooth) {
                mv = new VoteBoxBoothView(model, view, (VoteBoxBooth) m);
            }
            views.put(m, mv);
            return mv;
        }
    }

}
