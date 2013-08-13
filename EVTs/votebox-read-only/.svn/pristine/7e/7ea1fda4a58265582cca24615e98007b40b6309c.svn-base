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

import sexpression.ASExpression;
import verifier.value.*;
import verifier.*;

public abstract class Comparison extends AST {
	public abstract Value compare(int left, int right);

	private final AST _left;

	private final AST _right;

	protected Comparison(ASExpression from, AST left, AST right) {
		super(from);
		_left = left;
		_right = right;
	}

	public Value eval(ActivationRecord environment) {
		final Value left = _left.eval(environment);
		final Value right = _right.eval(environment);
		return left.execute(new AValueVisitor() {

			@Override
			public Value forInt(final IntValue left) {
				return right.execute(new AValueVisitor() {

					@Override
					public Value forInt(IntValue right) {
						return compare(left.get(), right.get());
					}

				});
			}

		});
	}
}
