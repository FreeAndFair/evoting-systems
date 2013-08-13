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
 * Each type of AST node must define a corresponding factory. The factory is
 * used by the parser to construct instances of the given AST type. AST
 * factories are the means by which primitives are pluggable -- plugins provide
 * the parser with factories in order to add support for new primitive types.
 * 
 * @author kyle
 * 
 */
public abstract class ASTFactory {

	/**
	 * Make an AST instance.
	 * 
	 * @param from
	 *            This is the s-expression that was encountered (matchresult is
	 *            the result of getPattern().match(this)
	 * @param matchresult
	 *            This is the result of the match operation of this factory's
	 *            pattern on the expression being parsed.
	 * @param parser
	 *            This is the parser doing the parsing.
	 * @return This method returns the newly constructed .
	 */
	public abstract AST make(ASExpression from, ListExpression matchresult,
			ASTParser parser);

	/**
	 * @return Get the pattern that defines which AST types this factory knows
	 *         how to make.
	 */
	public abstract String getPattern();

	/**
	 * @return This method returns the name of the target binary operation.
	 */
	public abstract String getName();

	private ASExpression _pattern;

	/**
	 * Get the ASE representation of the pattern string (the result of
	 * this.getPattern()). This value is lazily computed and cached.
	 * 
	 * @return This method returns the ASE representation of the pattern string.
	 */
	public ASExpression getPatternASE() {
		if (_pattern == null)
			_pattern = ASExpression.make(getPattern());
		return _pattern;
	}
}
