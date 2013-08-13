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

public class Print extends AST {

	public static final ASTFactory FACTORY = new ListArgFactory(
			new IConstructor() {

				public AST make(ASExpression from, AST... args) {
					return new Print(from, args);
				}
			}) {

		@Override
		public String getName() {
			return "print";
		}
	};

	private final AST[] _args;

	private Print(ASExpression from, AST[] args) {
		super(from);
		_args = args;
	}

	public Value eval(ActivationRecord environment) {
		StringBuffer buf = new StringBuffer();

		boolean first = true;
		for (AST a : _args) {
			if (first)
				first = false;
			else
				buf.append(" ");

			Value evaluated = a.eval(environment);
			Value result = evaluated.execute(new AValueVisitor() {
				public Value forExpression(Expression ase) {
					return ase;
				}

				public Value forFalse(False f) {
					return f;
				}

				public Value forInt(IntValue i) {
					return i;
				}

				public Value forSet(SetValue s) {
					return s;
				}

				public Value forTrue(True t) {
					return t;
				}

				public Value forDAG(DAGValue d) {
					return d;
				}

				public Value forReduction(Reduction ast) {
					return ast;
				}
			});
			buf.append(result.toString());
		}
		System.out.println(buf.toString());
		return True.SINGLETON;
	}
}
