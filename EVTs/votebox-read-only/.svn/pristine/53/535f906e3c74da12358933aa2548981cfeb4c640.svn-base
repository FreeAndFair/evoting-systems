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

import verifier.*;
import verifier.value.*;

/**
 * This AST node represents the "exists" quantifier.
 * 
 * @author kyle
 * 
 */
public class Exists extends Quantifier {

	public static final ASTFactory FACTORY = new QuantifierFactory(
			new IQuantifierConstructor() {

				public AST make(String name, AST set, AST body, int index,
						ArrayList<Binding<AST, ActivationRecord>> map) {
					return new Exists(name, set, body, index, map);
				}
			}) {

		@Override
		public String getName() {
			return "exists";
		}
	};

	public static final ASTFactory PFACTORY = new PQuantifierFactory(
			new IQuantifierConstructor() {

				public AST make(String name, AST set, AST body, int index,
						ArrayList<Binding<AST, ActivationRecord>> map) {
					return new Exists(name, set, body, index, map);
				}
			}) {

		@Override
		public String getName() {
			return "pexists";
		}
	};

	public Exists(String name, AST set, AST body, int index,
			ArrayList<Binding<AST, ActivationRecord>> unknowns) {
		super(name, set, body, index, unknowns);
	}

	@Override
	public void forEvalFalse(Box<Boolean> box) {
	}

	@Override
	public void forEvalTrue(Box<Boolean> box) {
		box.set(true);
	}

	@Override
	public Value result(Box<Boolean> box, boolean sealed,
			ArrayList<Binding<AST, ActivationRecord>> newUnknowns,
			Box<Integer> newIndex) {
		if (box.get().booleanValue() == true)
			return True.SINGLETON;
		if (sealed && newUnknowns.size() == 0)
			return False.SINGLETON;
		return new Reduction(new Exists(_name, _set, _body, newIndex.get(),
				newUnknowns));
	}

	@Override
	public String getPName() {
		return "pexists";
	}
}
