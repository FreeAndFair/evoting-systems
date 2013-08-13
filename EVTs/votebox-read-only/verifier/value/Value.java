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

package verifier.value;

import sexpression.*;

/**
 * An IValue represents an internal verifier value. These are values which can
 * be represented in the rules language, and include integers, truth, falsity,
 * sets, DAGs, closures (functions as values), expressions (these are arbitrary
 * s-expressions), or suspensions.
 * 
 * @see verifier.value.IntValue
 * @see verifier.value.TruthValue
 * @see verifier.value.SetValue
 * @see verifier.value.DAGValue
 * @see verifier.value.Closure
 * @see verifier.value.Expression
 * @see verifier.ISuspension
 * 
 * @author derrley
 * 
 */
public abstract class Value {

	/**
	 * Each concrete value class must implement this visitor hook method.
	 * 
	 * @param visitor
	 *            Execute this visitor on the target.
	 * @return This method will relay the return value of the visitor.
	 */
	public abstract Value execute(IValueVisitor visitor);

	/**
	 * Convert this value to a serializable s-expression format.
	 * 
	 * @return This method returns the s-expression format for the target value.
	 */
	public abstract ASExpression toASE();

	private boolean _sealed;

	/**
	 * @param sealed
	 *            This is the initial sealed state of the value.
	 */
	protected Value(boolean sealed) {
		_sealed = sealed;
	}

	/**
	 * Seal the value, denoting that no new information will ever arrive.
	 */
	public void seal() {
		_sealed = true;
	}

	/**
	 * @return This method returns true if the value has been sealed or false if
	 *         it has not been.
	 */
	public boolean isSealed() {
		return _sealed;
	}
}
