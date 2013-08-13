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

import java.util.HashMap;

import sexpression.*;

import verifier.*;

/**
 * Parse an AST from an s-expression representation. AST instances are
 * constructed from factories. Each factory defines an s-expression pattern
 * which the parser uses to match s-expression instances with their
 * representative AST type.
 * 
 * @author kyle
 * 
 */
public class ASTParser {

	public static final ASTParser PARSER = new ASTParser(Verifier
			.getPrimitives(), Constant.FACTORY);

	private final HashMap<String, ASTFactory> _primfactories;

	private final ASTFactory _constfactory;

	/**
	 * @param primfactories
	 *            These factories construct the ASTs of primitive applications
	 *            (such as and, let, not, etc.)
	 * @param constfactory
	 *            This factory constructs the AST representation of a constant
	 * 
	 */
	public ASTParser(HashMap<String, ASTFactory> primfactories,
			ASTFactory constfactory) {
		_primfactories = primfactories;
		_constfactory = constfactory;
	}

	/**
	 * Parse an s-expression in string format.
	 * 
	 * @param expression
	 *            This is the expression that represents the AST.
	 * @return This method returns the AST representation of the string given.
	 */
	public AST parse(String expression) {
		return parse(ASExpression.make(expression));
	}

	/**
	 * Convert an s-expression into a representative AST.
	 * 
	 * @param expression
	 *            Convert this s-expression.
	 * @return This method returns the AST that represents the given expression.
	 */
	public AST parse(ASExpression expression) {
		// System.out.println("[astparse] " + expression);
		try {
			// constant/identifier case
			ASExpression matchresult = _constfactory.getPatternASE().match(
					expression);
			if (matchresult != NoMatch.SINGLETON)
				return _constfactory.make(expression,
						(ListExpression) matchresult, this);

			// primitive case - factory is keyed by the operation name
			if (expression instanceof ListExpression) {
				ASExpression zeroelt = ((ListExpression) expression).get(0);
				if (zeroelt instanceof StringExpression
						&& _primfactories.containsKey(zeroelt.toString())) {
					ASTFactory factory = _primfactories.get(zeroelt.toString());
					matchresult = factory.getPatternASE().match(expression);
					if (matchresult != NoMatch.SINGLETON)
						return factory.make(expression,
								(ListExpression) matchresult, this);
					throw new FormatException(expression, new Exception(
							"Arguments don't match " + factory.getPatternASE()));
				}
			}
			throw new FormatException(expression, new Exception(
					"This s-expression could not be parsed in any way"));
		} catch (ClassCastException e) {
			throw new FormatException(expression, e);
		} catch (IndexOutOfBoundsException e) {
			throw new FormatException(expression, e);
		}

	}
}
