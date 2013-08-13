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
import verifier.value.*;

public class Let extends AST {

	public static final ASTFactory FACTORY = new ASTFactory() {

		@Override
		public String getName() {
			return "let";
		}

		@Override
		public String getPattern() {
			return "(let #list:(#string #any) #any)";
		}

		@Override
		public AST make(ASExpression from, ListExpression matchresult,
				ASTParser parser) {
			ListExpression bindingsExpr = (ListExpression) (matchresult.get(0));
			int numBindings = bindingsExpr.size();
			ASExpression body = matchresult.get(1);

			AST[] bindings = new AST[numBindings];
			String[] variables = new String[numBindings];
			for (int lcv = 0; lcv < numBindings; lcv++) {
				ListExpression clause = (ListExpression) (bindingsExpr.get(lcv));
				variables[lcv] = ((StringExpression) (clause.get(0)))
						.toString();
				bindings[lcv] = parser.parse(clause.get(1));
			}
			return new Let(from, parser.parse(body), bindings, variables);
		}
	};

	public static final ASTFactory PFACTORY = new ASTFactory() {

		@Override
		public String getName() {
			return "plet";
		}

		@Override
		public String getPattern() {
			return "(plet #list:(#string #any) #any)";
		}

		@Override
		public AST make(ASExpression from, ListExpression matchresult,
				ASTParser parser) {
			return new Let(parser.parse(matchresult.get(1)),
					new ActivationRecord(matchresult.get(0)));
		}
	};

	private final AST _body;

	private AST[] _bindings;
	private String[] _variables;

	private ActivationRecord _record;

	private ASExpression _ase;

	private Let(ASExpression from, AST body, AST[] bindings, String[] variables) {
		super(from);
		_body = body;
		_bindings = bindings;
		_variables = variables;
	}

	public Let(AST body, ActivationRecord record) {
		super(null);
		_body = body;
		_record = record;
	}

	/**
	 * @see verifier.ast.AST#toASE()
	 */
	@Override
	public ASExpression toASE() {
		if (_record == null)
			return super.toASE();
		if (_ase == null)
			_ase = new ListExpression(StringExpression.make("plet"), _record
					.toASE(), _body.toASE());
		return _ase;
	}

	/**
	 * @see verifier.ast.AST#eval(verifier.ActivationRecord)
	 */
	@Override
	public Value eval(ActivationRecord environment) {
		ActivationRecord env;
		if (_record == null) {
			HashMap<String, Value> extension = new HashMap<String, Value>();
			for (int lcv = 0; lcv < _bindings.length; lcv++)
				extension
						.put(_variables[lcv], _bindings[lcv].eval(environment));
			env = environment.extend(extension);
		} else {
			env = _record;
		}

		Value v = _body.eval(env);
		if (v instanceof Reduction)
			return new Reduction(new Let(((Reduction) v).getAST(), env));
		return v;
	}
}
