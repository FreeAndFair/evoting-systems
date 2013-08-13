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

package votebox.middle.view;

/**
 * An event is our encapsulation of an input device event.
 * 
 * @author Kyle
 * 
 */
public class InputEvent {

    /**
     * Use this to refer to input events that don't involve a drawable.
     */
    public static final InputEvent NONE = new InputEvent( null );

    private final IDrawable _focused;

    /**
     * This is the public constructor for Event.
     * 
     * @param focused
     *            This is the drawable that the mouse is currently focused on.
     */
    public InputEvent(IDrawable focused) {
        _focused = focused;
    }    
    /**
     * Call this method to get the drawable that was being pointed at by the
     * mouse at the time the event happened.
     * Note that if there is a payload, there is NOT a focusedDrawable and vice versa.
     * 
     * @return This method returns the drawable that was being pointed at by the
     *         mouse, or null if the mouse was not pointing to anything.
     */
    public IDrawable focusedDrawable() {
        return _focused;
    }
}
