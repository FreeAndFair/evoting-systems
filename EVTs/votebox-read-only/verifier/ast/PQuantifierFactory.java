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

import sexpression.*;

public abstract class PQuantifierFactory extends ASTFactory {
	private IQuantifierConstructor _constructor;

	protected PQuantifierFactory(IQuantifierConstructor constructor) {
		_constructor = constructor;
	}

	/**
	 * @see verifier.ast.ASTFactory#make(sexpression.ListExpression,
	 *      verifier.ast.ASTParser)
	 */
	@Override
	public AST make(ASExpression from, ListExpression matchresult,
			ASTParser parser) {
		ArrayList<Binding<AST, ActivationRecord>> bindings = new ArrayList<Binding<AST, ActivationRecord>>();
		ListExpression list = (ListExpression) matchresult.get(4);
		for (ASExpression ase : list) {
			ListExpression binding = (ListExpression) ase;
			bindings.add(new Binding<AST, ActivationRecord>(parser
					.parse(binding.get(0)),
					new ActivationRecord(binding.get(1))));
		}

		return _constructor.make(matchresult.get(0).toString(), parser
				.parse(matchresult.get(1)), parser.parse(matchresult.get(2)),
				Integer.parseInt(matchresult.get(3).toString()), bindings);
	}

	/**
	 * @see verifier.ast.ASTFactory#getPattern()
	 */
	@Override
	public String getPattern() {
		return "(" + getName() + " #string #any #any #string #list:(#any #list:(#string #any)))";
	}
}
