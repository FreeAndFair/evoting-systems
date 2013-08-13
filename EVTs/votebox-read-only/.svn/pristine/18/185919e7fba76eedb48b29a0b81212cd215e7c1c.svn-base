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

package votebox.middle.ballot;

/**
 * 
 * 
 * Card delegates to an implementation of this interface for its behavior
 * regarding what to do
 * 
 * This is the strategy implementation for KofN voting. KofN is the style of
 * voting that is done in a race where more than one candidate can be selected
 * as being preferred in the same race. The behavior of the gui components in
 * these types of races is synonymous to a group of checkboxes in a windows
 * environment, where only "k out of n" checkboxes can be selected at one time.
 * 
 */

public class KofN extends ACardStrategy {
	/**
	 * This field is the maximum number of elements who can be selected in this
	 * race.
	 * 
	 */
	private int _maxNumber;

	/**
	 * This field is the number of elements who are currently selected in this
	 * race.
	 * 
	 */
	private int _count = 0;

	public KofN(int max) {
		_maxNumber = max;
	}

	/**
	 * If this race has room for another selected candidate, then tell
	 * the candidate to Select itself.
	 * @param element This element wants to be selected.
	 */
	public boolean select(SelectableCardElement element) {
		if (_count + 1 <= _maxNumber) {
			_count++;
			element.setSelected(true);
			return true;
		}
		return false;
	}

	/**
	 * Decrement the count and tell the element to Select itself.
	 * @param element selectable element to deselect
	 */
	public boolean deselect(SelectableCardElement element) {
		if (_count - 1 >= 0) {
			_count--;
			element.setSelected(false);
			return true;
		}
		return false;
	}
}