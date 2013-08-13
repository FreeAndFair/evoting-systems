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
 * This exception is thrown by Properties if the format given for a certain type
 * cannot be decoded to mean anything reasonable.
 * 
 * @author Kyle
 * 
 */
public class UnknownFormatException extends Exception {

	/**
	 * This is the default serial version UID.
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * This is the type for which the value could not be decoded.
	 */
	private String _type;

	/**
	 * This is the value that could not be decoded.
	 */
	private String _value;

	/**
	 * This is the public constructor for UnknownFormatException
	 * 
	 * @param type
	 *            This is the type for which the value cannot be determined.
	 * @param value
	 *            This is the value which cannot be properly decoded.
	 */
	public UnknownFormatException(String type, String value) {
		super("Could not decode " + value + " to mean anything for type "
				+ type);
		_type = type;
		_value = value;
	}

	/**
	 * This is the getter for _type
	 * 
	 * @return _type
	 */
	public String getType() {
		return _type;
	}

	/**
	 * This is the getter for _value
	 * 
	 * @return _value
	 */
	public String getValue() {
		return _value;
	}
}
