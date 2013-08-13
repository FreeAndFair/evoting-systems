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
import sexpression.ListExpression;

/**
 * Instances of this class are factories for primitives that have one argument
 * which is a list ('and' and 'or').
 * 
 * @author kyle
 * 
 */
public abstract class ListArgFactory extends ASTFactory {

	private IConstructor _constructor;

	protected ListArgFactory(IConstructor constructor) {
		_constructor = constructor;
	}

	/**
	 * @see verifier.ast.ASTFactory#make(sexpression.ListExpression,
	 *      verifier.ast.ASTParser)
	 */
	@Override
	public AST make(ASExpression from, ListExpression matchresult,
			ASTParser parser) {
		ArrayList<AST> args = new ArrayList<AST>();
		for (ASExpression exp : (ListExpression) matchresult.get(0))
			args.add(parser.parse(exp));
		return _constructor.make(from, args.toArray(new AST[0]));
	}

	/**
	 * @see verifier.ast.ASTFactory#getPattern()
	 */
	@Override
	public String getPattern() {
		return "(" + getName() + " #list:#any)";
	}
}
