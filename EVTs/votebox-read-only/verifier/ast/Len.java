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

public class Len extends AST {

	public static final ASTFactory FACTORY = new PrimFactory(1,
			new IConstructor() {

				public AST make(ASExpression from, AST... args) {
					return new Len(from, args[0]);
				}
			}) {

		@Override
		public String getName() {
			return "len";
		}
	};

	private final AST _arg;

	private Len(ASExpression from, AST arg) {
		super(from);
		_arg = arg;
	}

	public Value eval(ActivationRecord environment) {
		Value arg = _arg.eval(environment);

		return arg.execute(new AValueVisitor() {

			@Override
			public Value forSet(SetValue s) {
				return new IntValue(s.size());
			}

			@Override
			public Value forExpression(Expression exp) {
				return new IntValue(exp.getASE().size());
			}

			@Override
			public Value forDAG(DAGValue d) {
				return new IntValue(d.size());
			}

		});
	}

}
