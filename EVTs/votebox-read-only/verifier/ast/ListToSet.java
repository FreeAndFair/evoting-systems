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
 * This AST represents an application of the "convert" primitive.
 * 
 * @author kyle
 * 
 */
public class ListToSet extends AST {

	public static final ASTFactory FACTORY = new PrimFactory(1,
			new IConstructor() {

				public AST make(ASExpression from, AST... args) {
					return new ListToSet(from, args[0]);
				}
			}) {

		@Override
		public String getName() {
			return "list->set";
		}
	};

	private final AST _arg;

	private ListToSet(ASExpression from, AST arg) {
		super(from);
		_arg = arg;
	}

	/**
	 * @see verifier.ast.AST#eval(verifier.ActivationRecord)
	 */
	@Override
	public Value eval(ActivationRecord environment) {
		Value arg = _arg.eval(environment);

		return arg.execute(new AValueVisitor() {

			@Override
			public Value forExpression(Expression e) {
				ASExpression expression = e.getASE();
				if (!(expression instanceof ListExpression))
					throw new UnexpectedTypeException(e, "list");
				ListExpression list = (ListExpression) expression;

				Expression[] exps = new Expression[list.size()];
				for (int lcv = 0; lcv < exps.length; lcv++)
					exps[lcv] = new Expression(list.getArray()[lcv]);
				SetValue sv = new SetValue(exps);
				sv.seal();
				return sv;
			}

		});
	}

}
