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
import verifier.*;
import verifier.value.*;

/**
 * Handles (succeeds [left] [right] [dag]) True if left succeeds right in the
 * given dag.
 * 
 * @author kyle
 * 
 */
public class Precedes extends AST {

	public static final ASTFactory FACTORY = new PrimFactory(3,
			new IConstructor() {

				public AST make(ASExpression from, AST... args) {
					return new Precedes(from, args[0], args[1], args[2]);
				}
			}) {

		@Override
		public String getName() {
			return "precedes";
		}
	};

	private final AST _left;
	private final AST _right;
	private final AST _dag;

	private Precedes(ASExpression from, AST left, AST right, AST dag) {
		super(from);
		_left = left;
		_right = right;
		_dag = dag;
	}

	public Value eval(ActivationRecord environment) {
		final Value left = _left.eval(environment);
		final Value right = _right.eval(environment);
		final Value dag = _dag.eval(environment);

		return dag.execute(new AValueVisitor() {

			@Override
			public Value forDAG(final DAGValue dag) {
				return left.execute(new AValueVisitor() {

					@Override
					public Value forExpression(final Expression left) {
						return right.execute(new AValueVisitor() {

							@Override
							public Value forExpression(Expression right) {
								// try {
								return dag.precedes(left, right) ? True.SINGLETON
										: False.SINGLETON;
								// }
								/*
								 * Not entirely sure why you were ever throwing
								 * this
								 */
								// catch (IncorrectFormatException e) {
								// Bugout
								// .err( "Incorrectly formatted message "
								// + "(couldn't parse message pointer info) in:
								// (precedes "
								// + left.toString()
								// + " "
								// + right.toString() + ")" );
								// e.printStackTrace();
								// }
							}
						});
					}

				});
			}

		});
	}
}
