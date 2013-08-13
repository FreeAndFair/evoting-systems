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

import sexpression.ASExpression;

/**
 * Abstract superclass for all DAGs-of-time to be used by the verifier. Some
 * implementations (ExplicitDAG) model an arbitrary DAG explicitly, while others
 * (FastDAG) use optimizations that require certain constraints on the input.
 * Either way, the public interface consists (in essence) of the single
 * predicate precedes(x,y): does x precede y in time?
 */
public abstract class DAGValue extends Value {
	public DAGValue() {
		super(/* sealed */false);
	}

	public abstract boolean precedes(Expression leftMessage,
			Expression rightMessage);

	/**
	 * @see verifier.value.Value#execute(verifier.value.IValueVisitor)
	 */
	@Override
	public Value execute(IValueVisitor visitor) {
		return visitor.forDAG(this);
	}

	/**
	 * @see verifier.value.Value#toASE()
	 */
	@Override
	public ASExpression toASE() {
		throw new RuntimeException("Cannot serialize a DAG");
	}

	/**
	 * Lookup the number of nodes in this dag.
	 * 
	 * @return This method returns the number of nodes in this dag.
	 */
	public abstract int size();

	/** String representation. */
	public String toString() {
		return "<value.DAGValue: size=" + size() + ">";
	}

	/** Enable the internal cache, if available. */
	public abstract void enableCache();

	/** Disable the internal cache, if available. */
	public abstract void disableCache();

}
