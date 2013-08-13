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
 * This is the button state which is "default," or is the state that the button
 * is in when it is not currently being focused on.
 */

public class DefaultButtonState extends AButtonState {
    /**
     * Singleton Design Pattern.
     * 
     */
    public static DefaultButtonState Singleton = new DefaultButtonState();

    /**
     * Singleton Design Pattern
     */
    private DefaultButtonState() {}

    /**
     * When the Button wishes to be focused, switch to the focused state
     */
    public void focus(Button context) {
        context.setState( FocusedButtonState.Singleton );
        context.getFocusedEvent().notifyObservers();
    }

    /**
     * When the Button wishes to be unfocused, do nothing, it is already
     * unfocused.
     */
    public void unfocus(Button context) {
    // NO-OP
    }

    /**
     * @see votebox.middle.view.widget.AButtonState#getImage(votebox.middle.view.widget.Button)
     */
    @Override
    public IViewImage getImage(Button context) {
        return context.getDefaultImage();
    }
}
