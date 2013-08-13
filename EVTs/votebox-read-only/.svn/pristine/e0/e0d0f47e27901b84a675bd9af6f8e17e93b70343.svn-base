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

import verifier.ast.*;
import sexpression.*;

/**
 * The verifier will evaluate an AST to a reduction if there isn't enough
 * information to evaluate what the rule asks for. The wrapped AST is a simpler
 * problem than was given (a reduction).
 * 
 * @author kyle
 * 
 */
public class Reduction extends Value {

	private final AST _ast;

	/**
	 * @param ast
	 *            This is the wrapped AST
	 */
	public Reduction(AST ast) {
		super(true);
		_ast = ast;
	}

	/**
	 * @return This method returns the AST that represents the reduction.
	 *         Evaluate this AST in an attempt to "try again" with the
	 *         verification.
	 */
	public AST getAST() {
		return _ast;
	}

	/**
	 * @see verifier.value.Value#execute(verifier.value.IValueVisitor)
	 */
	@Override
	public Value execute(IValueVisitor visitor) {
		return visitor.forReduction(this);
	}

	@Override
	public ASExpression toASE() {
		return new ListExpression(StringExpression.make("red"), _ast.toASE());
	}

	@Override
	public String toString() {
		return toASE().toString();
	}
}
