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

import votebox.middle.view.IViewImage;

/**
 * This class deifnes the abstract state for a ToggleButton (used in state
 * pattern). ToggleButtons delegate certain state-dependent behaviors to an
 * instance of this class.
 */
public abstract class AToggleButtonState {

    /**
     * Because the image that is used to represent a toggle button is
     * state-speciffic, getImage is delegated here.
     * 
     * @param context
     *            This is the button that is delegating.
     * @return This method returns the state-specific image that represents the
     *         delegating button.
     */
    public abstract IViewImage getImage(ToggleButton context);

    /**
     * The SelectableCardElement delegates to this method when it is told that
     * the user has chosen it to be toggled.
     * 
     * @param context
     *            This is the button that is delegating.
     */
    public abstract void select(ToggleButton context);

    /**
     * Explicitly selects the element who delegates to this state object. This
     * will happen regardless of the current state.
     * 
     * @param context
     *            This is the button that is delegating.
     */
    public abstract void makeSelected(ToggleButton context);

    /**
     * Explicitly deselects the element who delegates to this state object. Thi
     * swill happen regardless of the current state.
     * 
     * @param context
     *            This is the button that is delegating.
     */
    public abstract void makeDeselected(ToggleButton context);

    /**
     * The SelectableCardElement delegates to this method when it is told that
     * the user is currently focused on it.
     * 
     * @param context
     *            This is the button that is delegating.
     */
    public abstract void focus(ToggleButton context);

    /**
     * The SelectableCardElement delegates to this method when it is told that
     * the user is no longer focused on it.
     * 
     * @param context
     *            This is the button that is delegating.
     */
    public abstract void unfocus(ToggleButton context);

}
