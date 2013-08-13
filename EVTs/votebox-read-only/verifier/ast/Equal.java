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

import sexpression.*;
import verifier.*;
import verifier.value.*;

/**
 * This AST represents an application of the equals primitive.
 * 
 * @author kyle
 * 
 */
public class Equal extends AST {

	public static final ASTFactory FACTORY = new PrimFactory(2,
			new IConstructor() {

				public AST make(ASExpression from, AST... args) {
					return new Equal(from, args[0], args[1]);
				}
			}) {

		@Override
		public String getName() {
			return "=";
		}
	};

	private final AST _left;

	private final AST _right;

	private Equal(ASExpression from, AST left, AST right) {
		super(from);
		_left = left;
		_right = right;
	}

	/**
	 * @see verifier.ast.AST#eval(verifier.ActivationRecord)
	 */
	@Override
	public Value eval(ActivationRecord environment) {
		final Value l = _left.eval(environment);
		final Value r = _right.eval(environment);

		return l.execute(new AValueVisitor() {

			@Override
			public Value forInt(final IntValue left) {
				return r.execute(new AValueVisitor() {

					@Override
					public Value forInt(IntValue right) {
						if (left.get() == right.get()) {
							return True.SINGLETON;
						} else {
							return False.SINGLETON;
						}

					}

					@Override
					public Value forSet(SetValue set) {
						return False.SINGLETON;
					}

					@Override
					public Value forExpression(Expression exp) {
						return False.SINGLETON;
					}

					@Override
					public Value forTrue(True t) {
						return False.SINGLETON;
					}

					@Override
					public Value forFalse(False f) {
						return False.SINGLETON;
					}
				});
			}

			@Override
			public Value forSet(final SetValue left) {
				return r.execute(new AValueVisitor() {

					@Override
					public Value forSet(SetValue right) {
						if (left.equals(right)) {
							return True.SINGLETON;
						} else {
							return False.SINGLETON;
						}
					}

					@Override
					public Value forInt(IntValue i) {
						return False.SINGLETON;
					}

					@Override
					public Value forExpression(Expression e) {
						return False.SINGLETON;
					}

					@Override
					public Value forTrue(True t) {
						return False.SINGLETON;
					}

					@Override
					public Value forFalse(False f) {
						return False.SINGLETON;
					}

				});
			}

			@Override
			public Value forExpression(final Expression left) {
				return r.execute(new AValueVisitor() {

					@Override
					public Value forExpression(Expression right) {
						if (left.equals(right)) {
							return True.SINGLETON;
						} else {
							return False.SINGLETON;
						}
					}

					@Override
					public Value forInt(IntValue i) {
						return False.SINGLETON;
					}

					@Override
					public Value forSet(SetValue set) {
						return False.SINGLETON;
					}

					@Override
					public Value forTrue(True t) {
						return False.SINGLETON;
					}

					@Override
					public Value forFalse(False f) {
						return False.SINGLETON;
					}
				});
			}

			@Override
			public Value forTrue(True t) {
				return r.execute(new AValueVisitor() {

					@Override
					public Value forExpression(Expression right) {
						return False.SINGLETON;
					}

					@Override
					public Value forInt(IntValue i) {
						return False.SINGLETON;
					}

					@Override
					public Value forSet(SetValue set) {
						return False.SINGLETON;
					}

					@Override
					public Value forTrue(True t) {
						return True.SINGLETON;
					}

					@Override
					public Value forFalse(False f) {
						return False.SINGLETON;
					}
				});
			}

			@Override
			public Value forFalse(False f) {
				return r.execute(new AValueVisitor() {

					@Override
					public Value forExpression(Expression right) {
						return False.SINGLETON;
					}

					@Override
					public Value forInt(IntValue i) {
						return False.SINGLETON;
					}

					@Override
					public Value forSet(SetValue set) {
						return False.SINGLETON;
					}

					@Override
					public Value forTrue(True t) {
						return False.SINGLETON;
					}

					@Override
					public Value forFalse(False f) {
						return True.SINGLETON;
					}
				});
			}
		});
	}
}
