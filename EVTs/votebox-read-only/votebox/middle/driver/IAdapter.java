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

package votebox.middle.driver;

import votebox.middle.Properties;

/**
 * This interface defines a general adapter that the
 * 
 * @author Kyle
 * 
 */
public interface IAdapter {

	/**
	 * Call this method to ask that a specific element be selected.
	 * 
	 * @param uid
	 *            Ask to select a card element that has this UID.
	 * @return This method returns true if the selection was a success (if it
	 *         was allowed), and false otherwise.
	 * @throws UnknownUIDException
	 *             This method throws when the UID that is given as a parameter
	 *             is not defined.
	 */
	public boolean select(String uid) throws UnknownUIDException, SelectionException;

	/**
	 * Call this method to ask that a specific element be deselected.
	 * 
	 * @return This method returns true if the deselection was a success (if it
	 *         was allowed), and false otherwise.
	 * @param uid
	 *            Ask to deselect a card element that has this UID.
	 * @throws UnknownUIDException
	 *             This method throws when the UID that is given as a parameter
	 *             is not defined.
	 */
	public boolean deselect(String uid) throws UnknownUIDException, DeselectionException;

	/**
	 * Call this method to get properties.
	 * 
	 * @return This method returns properties.
	 */
	public Properties getProperties();
}
