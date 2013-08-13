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
 * This exception is thrown when an assumption is made about a type that is
 * false. This exception is notably used in Properties. If one invokes get*(...)
 * where * is any type other than object, if the actual type doesn't agree with *,
 * the method will throw an instance of this exception.
 * 
 * @author Kyle
 * 
 */
public class IncorrectTypeException extends Exception {

	/**
	 * This is the default serial version uid.
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * This is the string representation for the type that was expected.
	 */
	private String _expected;

	/**
	 * This is the string representation for the actual type.
	 */
	private String _actual;

	/**
	 * This is the public constructor for IncorrectTypeException.
	 * 
	 * @param expected
	 *            This is the string representation for the type that was
	 *            expected.
	 * @param actual
	 *            This is the string representation for the actual type.
	 */
	public IncorrectTypeException(String expected, String actual) {
		super("Expected type " + expected + " but was type " + actual);
		_expected = expected;
		_actual = actual;
	}

	/**
	 * This is the getter for _expected.
	 * 
	 * @return _expected
	 */
	public String getExpected() {
		return _expected;
	}

	/**
	 * This is the getter for _actual
	 * 
	 * @return _actual
	 */
	public String getActual() {
		return _actual;
	}
}
