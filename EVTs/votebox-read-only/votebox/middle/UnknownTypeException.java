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

package votebox.middle;

/**
 * This method is thrown by Properties when it encounters a type it doesn't know
 * about.
 * 
 * @author Kyle
 * 
 */
public class UnknownTypeException extends Exception {

	/**
	 * Default Serial Version UID
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * This is the type that was unknown.
	 */
	private String _type;

	/**
	 * This is the public constructor for UnknownTypeException
	 * 
	 * @param type
	 *            This is the string representation of the type that is unknown
	 */
	public UnknownTypeException(String type) {
		super(type + " is an unknown type. Properties must be declared as "
				+ "Integer, String, or Boolean");
		_type = type;
	}

	/**
	 * This is the getter for _type.
	 * 
	 * @return _type.
	 */
	public String getType() {
		return _type;
	}
}
