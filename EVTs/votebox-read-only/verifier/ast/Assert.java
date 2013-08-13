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

/**
 * (assert name expected actual)
 * 
 * @author kyle
 */
public class Assert extends AST {

	/**
	 * This maps assertion names to variable bindings which caused the failure.
	 */
	public static final ArrayList<AssertionFailure> FAILED_ASSERTIONS = new ArrayList<AssertionFailure>();

	public static final ASTFactory FACTORY = new ASTFactory() {

		@Override
		public String getName() {
			return "assert";
		}

		@Override
		public String getPattern() {
			return "(assert #string #any #any)";
		}

		@Override
		public AST make(ASExpression from, ListExpression matchresult,
				ASTParser parser) {
			return new Assert(from, matchresult.get(0).toString(), parser
					.parse(matchresult.get(1)), parser
					.parse(matchresult.get(2)));
		}
	};

	private final String _name;

	private final AST _expected;

	private final AST _actual;

	private Assert(ASExpression from, String name, AST expected, AST body) {
		super(from);
		_name = name;
		_expected = expected;
		_actual = body;
	}

	@Override
	public Value eval(ActivationRecord environment) {
		final Value expected = _expected.eval(environment);
		final Value actual = _actual.eval(environment);
		if (expected.equals(actual))
			return actual;

		FAILED_ASSERTIONS.add(new AssertionFailure(_name, environment,
				expected, actual));
		return actual;
	}

}
