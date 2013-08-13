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

package votebox.middle.view.widget;

/**
 * This class encapsulates the notion of the strategy which a toggle button
 * group uses to determine whether or not to accept a toggle button's request to
 * either select itself or deselect itself.
 * 
 * @author Kyle
 * 
 */
public abstract class AToggleButtonGroupStrategy {

    /**
     * A toggle button calls this method to ask to be selected. If an
     * implementing strategy allows the selection to be made, it should call the
     * button's makeSelected(...) method.
     * 
     * @param context
     *            This is the button that wishes to be selected.
     */
    public abstract void select(ToggleButton context);

    /**
     * A toggle button calls this method to ask to be deselected. If an
     * implementing strategy allows this deselection to be made, it should call
     * the button's makeDeselected(...) method.
     * 
     * @param context
     *            This is the button that wishes to be deselected.
     */
    public abstract void deselect(ToggleButton context);
}
