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

package verifier.ast;

import verifier.*;
import verifier.value.*;

import sexpression.*;

/**
 * Instances which implement IAST represent concrete nodes in an abstract syntax
 * tree.
 * 
 * @author kyle
 * 
 */
public abstract class AST {

	/**
	 * Evaluate the target expression given the passed environment.
	 * 
	 * @param environment
	 *            Lookup non-primitive identifiers in this environment.
	 * @return This method returns the result of the evaluation.
	 */
	public abstract Value eval(ActivationRecord environment);

	private final ASExpression _ase;

	/**
	 * @param ase
	 *            Extending classes must provide the representative s-expression
	 *            for any newly constructed AST. This should simply be the
	 *            expression that the AST was parsed from.
	 */
	protected AST(ASExpression ase) {
		_ase = ase;
	}

	/**
	 * @return Convert this AST to s-expression format (This is the
	 *         representation it was originally parsed out of).
	 */
	public ASExpression toASE() {
		return _ase;
	}
}
