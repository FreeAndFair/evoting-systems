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
 * This is the
 */

public class FocusedButtonState extends AButtonState {
	/**
	 * Singleton Design Pattern
	 */
	public static FocusedButtonState Singleton = new FocusedButtonState();

	/**
	 * Singleton Design Pattern
	 */
	private FocusedButtonState() {
	}

	/**
	 * When the button asks to be focused, do nothing, it already is.
	 */
	public void focus(Button context) {
		// NO-OP
	}

	/**
	 * When the button asks to be unfocused, change the button's state to
	 * default.
	 */
	public void unfocus(Button context) {
		context.setState(DefaultButtonState.Singleton);
		context.getUnfocusedEvent().notifyObservers();
	}

	/**
	 * @see votebox.middle.view.widget.AButtonState#getImage(votebox.middle.view.widget.Button)
	 */
	@Override
	public IViewImage getImage(Button context) {
		return context.getFocusedImage();
	}
}