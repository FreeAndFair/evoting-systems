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

import sexpression.*;
import verifier.*;
import verifier.value.*;

public abstract class ListArgConnective extends AST {

	public abstract Value result(Box<Boolean> box, ArrayList<AST> unknowns);

	public abstract void forEvalTrue(Box<Boolean> box);

	public abstract void forEvalFalse(Box<Boolean> box);

	private final AST[] _args;

	private ASExpression _ase;

	protected ListArgConnective(AST[] args) {
		super(null);
		_args = args;
	}

	/**
	 * @see verifier.ast.AST#toASE()
	 */
	@Override
	public ASExpression toASE() {
		if (_ase == null) {
			ASExpression[] arr = new ASExpression[_args.length];
			for (int lcv = 0; lcv < arr.length; lcv++)
				arr[lcv] = _args[lcv].toASE();
			_ase = new ListExpression(arr);
		}
		return _ase;
	}

	/**
	 * @see verifier.ast.AST#eval(verifier.ActivationRecord)
	 */
	@Override
	public Value eval(ActivationRecord environment) {
		final Box<Boolean> box = new Box<Boolean>(false);
		final ArrayList<AST> unknowns = new ArrayList<AST>();

		for (final AST ast : _args) {
			ast.eval(environment).execute(new AValueVisitor() {

				@Override
				public Value forTrue(True t) {
					forEvalTrue(box);
					return null;
				}

				@Override
				public Value forFalse(False f) {
					forEvalFalse(box);
					return null;
				}

				@Override
				public Value forReduction(Reduction reduction) {
					unknowns.add(reduction.getAST());
					return null;
				}

			});
		}

		return result(box, unknowns);
	}
}
