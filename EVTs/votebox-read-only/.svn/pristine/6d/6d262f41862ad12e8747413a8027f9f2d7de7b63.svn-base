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

import verifier.*;
import verifier.value.*;

import sexpression.*;

public class LetMatch extends AST {

	public static final ASTFactory FACTORY = new PrimFactory(4,
			new IConstructor() {

				public AST make(ASExpression from, AST... args) {
					return new LetMatch(from, args[0], args[1], args[2],
							args[3]);
				}
			}) {

		@Override
		public String getName() {
			return "let-match";
		}
	};

	private final AST _pattern;
	private final AST _target;
	private final AST _body;
	private final AST _failureBody;

	private LetMatch(ASExpression from, AST pattern, AST target, AST body,
			AST failureBody) {
		super(from);
		_pattern = pattern;
		_target = target;
		_body = body;
		_failureBody = failureBody;
	}

	@Override
	public Value eval(final ActivationRecord environment) {
		final Value pattern = _pattern.eval(environment);
		final Value target = _target.eval(environment);

		return pattern.execute(new AValueVisitor() {

			@Override
			public Value forExpression(final Expression patternexp) {
				return target.execute(new AValueVisitor() {

					@Override
					public Value forExpression(Expression targetexp) {
						HashMap<String, ASExpression> match = patternexp
								.getASE().namedMatch(targetexp.getASE());

						if (match == NamedNoMatch.SINGLETON) {
							Value v = _failureBody.eval(environment);
							if (v instanceof Reduction)
								return new Reduction(new Let(((Reduction) v)
										.getAST(), environment));
							return v;
						}

						HashMap<String, Value> extension = new HashMap<String, Value>();
						for (String s : match.keySet())
							extension.put(s, new Expression(match.get(s)));
						ActivationRecord env = environment.extend(extension);

						Value v = _body.eval(env);
						if (v instanceof Reduction)
							return new Reduction(new Let(((Reduction) v)
									.getAST(), env));
						return v;
					}

				});
			}

		});
	}
}
