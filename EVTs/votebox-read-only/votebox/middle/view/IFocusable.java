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
 * Some IDrawables have additional view-related behavior which stems from the
 * fact that some IDrawables are actually "buttons," or user interface controls.
 * We term these controls "focusable," and make them implement the interface
 * IFocusable. This term stems from the fact that these controls must be able to
 * communicate to the user that he is currently "focused" on them--that if he
 * presses some type of "select" control, that he will chose the item that is
 * "focused." The view can communicate to an IFocusable whether it would like it
 * to be focused or unfocused by invoking the two functions defined here.
 */

public interface IFocusable extends IDrawable {
	
	/**
	 * Invoke this method to ask this focusable item to "focus" itself.
	 * 
	 */
	public abstract void focus();

	/**
	 * Invoke this method to ask this focusable item to "unfocus" itself.
	 */
	public abstract void unfocus();

	/**
	 * Invoke this method to tell this focusable item that the user has chosen
	 * (or selected) it.
	 */
	public abstract void select();

	/**
	 * Call this method to get the focusable that has been defined as being
	 * "above" this one.
	 * 
	 * @return This method returns the focusable that is "above" this one.
	 */
	IFocusable getUp();

	/**
	 * Call this method to define which focusable is "above" this one.
	 * 
	 * @param focusable
	 *            This is the focusable that will be defined as being "above"
	 *            this one.
	 */
	void setUp(IFocusable focusable);

	/**
	 * Call this method to get the focusable that has been defined as being
	 * "below" this one.
	 * 
	 * @return This method returns the focusable that is "below" this one.
	 */
	IFocusable getDown();

	/**
	 * Call this method to define which focusable is "below" this one.
	 * 
	 * @param focusable
	 *            This is the focusable that will be defined as being "below"
	 *            this one.
	 */
	void setDown(IFocusable focusable);

	/**
	 * Call this method to get the focusable that has been defined as being "to
	 * the left" of this one.
	 * 
	 * @return This method returns the focusable that is "to the left" of this
	 *         one.
	 */
	IFocusable getLeft();

	/**
	 * Call this method to define which focusable is "left of" this one.
	 * 
	 * @param focusable
	 *            This is the focusable that will be defined as being "left of"
	 *            this one.
	 */
	void setLeft(IFocusable focusable);

	/**
	 * Call this method to get the focusable that has been defined as being "to
	 * the right" of this one.
	 * 
	 * @return This method returns the focusable that is "to the right" of this
	 *         one.
	 */
	IFocusable getRight();

	/**
	 * Call this method to define which focusable is "right of" this one.
	 * 
	 * @param focusable
	 *            This is the focusable that will be defined as being "right of"
	 *            this one.
	 */
	void setRight(IFocusable focusable);

	/**
	 * Call this method to get the focusable that has been defined as being
	 * "after" this one, by some predefined sequence.
	 * 
	 * @return This method returns the focusable that has been defined as being
	 *         "after" this one, by some predefined sequence.
	 */
	IFocusable getNext();

	/**
	 * Call this method to define which focusable is "next after" this one.
	 * 
	 * @param focusable
	 *            This is the focusable that will be defined as being "next
	 *            after" this one.
	 */
	void setNext(IFocusable focusable);

	/**
	 * Call this method to get the focusable that has been defined as being
	 * "before" this one, by some predefined sequence.
	 * 
	 * @return This method returns the focusable that has been defined as being
	 *         "before" this one, by some predefined sequence.
	 */
	IFocusable getPrevious();

	/**
	 * Call this method to define which focusable is "previous before" this one.
	 * 
	 * @param focusable
	 *            This is the focusable that will be defined as being "previous
	 *            before" this one.
	 */
	void setPrevious(IFocusable focusable);
}