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

import java.util.ArrayList;

import sexpression.ASExpression;
import verifier.*;
import verifier.value.*;

public class Or extends ListArgConnective {

	public static final ASTFactory FACTORY = new ListArgFactory(
			new IConstructor() {

				public AST make(ASExpression from, AST... args) {
					return new Or(args);
				}
			}) {

		@Override
		public String getName() {
			return "or";
		}
	};

	protected Or(AST[] args) {
		super(args);
	}

	@Override
	public void forEvalFalse(Box<Boolean> box) {
	}

	@Override
	public void forEvalTrue(Box<Boolean> box) {
		box.set(true);
	}

	@Override
	public Value result(Box<Boolean> box, ArrayList<AST> unknowns) {
		if (box.get().booleanValue() == true)
			return True.SINGLETON;
		if (unknowns.size() > 0)
			return new Reduction(new Or(unknowns.toArray(new AST[0])));
		return False.SINGLETON;
	}

}
