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

/**
 * Instances of this class represent AST nodes that represent applications of
 * simple primitives. A simple primitive is one that is of the form ([name] arg1
 * arg2 ... argn) for some n number of arguments.
 * 
 * @author kyle
 * 
 */
public abstract class PrimFactory extends ASTFactory {

	private final IConstructor _constructor;

	private final int _args;

	protected PrimFactory(int args, IConstructor constructor) {
		_args = args;
		_constructor = constructor;
	}

	/**
	 * @see verifier.ast.ASTFactory#make(sexpression.ListExpression,
	 *      verifier.ast.ASTParser)
	 */
	@Override
	public AST make(ASExpression from, ListExpression matchresult,
			ASTParser parser) {
		AST[] args = new AST[_args];
		for (int lcv = 0; lcv < _args; lcv++)
			args[lcv] = parser.parse(matchresult.get(lcv));
		return _constructor.make(from, args);
	}

	/**
	 * @see verifier.ast.ASTFactory#getPattern()
	 */
	@Override
	public String getPattern() {
		StringBuffer buff = new StringBuffer();
		buff.append('(');
		buff.append(getName());
		for (int lcv = 0; lcv < _args; lcv++) {
			buff.append(" ");
			buff.append("#any");
		}
		buff.append(')');
		return buff.toString();
	}

}
