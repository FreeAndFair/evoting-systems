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
 * This AST node represents an application of the get primitive.
 * 
 * @author kyle
 * 
 */
public class Get extends AST {

	public static final ASTFactory FACTORY = new PrimFactory(2,
			new IConstructor() {

				public AST make(ASExpression from, AST... args) {
					return new Get(from, args[0], args[1]);
				}
			}) {

		@Override
		public String getName() {
			return "get";
		}
	};

	private final AST _num;

	private final AST _list;

	private Get(ASExpression from, AST num, AST list) {
		super(from);
		_num = num;
		_list = list;
	}

	/**
	 * @see verifier.ast.AST#eval(verifier.ActivationRecord)
	 */
	@Override
	public Value eval(ActivationRecord environment) {
		final Value number = _num.eval(environment);
		final Value list = _list.eval(environment);
		final AST outer = this;

		return number.execute(new AValueVisitor() {

			@Override
			public Value forInt(final IntValue numberval) {
				return list.execute(new AValueVisitor() {

					@Override
					public Value forExpression(Expression e) {
						ASExpression value = e.getASE();
						if (!(value instanceof ListExpression))
							throw new UnexpectedTypeException(list, "list");

						try {
							return new Expression(((ListExpression) value)
									.get(numberval.get()));
						} catch (IndexOutOfBoundsException error) {
							throw new IndexException(outer);
						}
					}

				});
			}

		});
	}
}
