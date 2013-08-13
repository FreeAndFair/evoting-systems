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
import verifier.*;
import verifier.value.*;

public class Impl extends AST {

	public static final ASTFactory FACTORY = new PrimFactory(2,
			new IConstructor() {

				public AST make(ASExpression from, AST... args) {
					return new Impl(args[0], args[1]);
				}
			}) {

		@Override
		public String getName() {
			return "impl";
		}
	};

	public static final ASTFactory AFACTORY = new PrimFactory(2,
			new IConstructor() {

				public AST make(ASExpression from, AST... args) {
					return new Impl(args[0].eval(ActivationRecord.END), args[1]);
				}
			}) {

		@Override
		public String getName() {
			return "aimpl";
		}
	};

	public static final ASTFactory CFACTORY = new PrimFactory(2,
			new IConstructor() {

				public AST make(ASExpression from, AST... args) {
					return new Impl(args[0], args[1].eval(ActivationRecord.END));
				}
			}) {

		@Override
		public String getName() {
			return "cimpl";
		}
	};

	private final AST _antecedent;
	private final AST _consequent;
	private Value _antecedentValue;
	private Value _consequentValue;

	private ASExpression _ase;

	public Impl(AST antecedent, AST consequent) {
		super(null);
		_antecedent = antecedent;
		_consequent = consequent;

		_antecedentValue = null;
		_consequentValue = null;
	}

	public Impl(Value antecedentValue, AST consequent) {
		super(null);
		_antecedent = null;
		_consequent = consequent;

		_antecedentValue = antecedentValue;
		_consequentValue = null;
	}

	public Impl(AST antecedent, Value consequentValue) {
		super(null);
		_antecedent = antecedent;
		_consequent = null;

		_antecedentValue = null;
		_consequentValue = consequentValue;
	}

	/**
	 * @see verifier.ast.AST#toASE()
	 */
	@Override
	public ASExpression toASE() {
		if (_ase == null) {
			if (_antecedentValue != null)
				_ase = new ListExpression(StringExpression.make("aimpl"),
						_antecedentValue.toASE(), _consequent.toASE());

			if (_consequentValue != null)
				_ase = new ListExpression(StringExpression.make("cimpl"),
						_antecedent.toASE(), _consequentValue.toASE());

			_ase = new ListExpression(StringExpression.make("impl"),
					_antecedent.toASE(), _consequent.toASE());
		}
		return _ase;
	}

	/**
	 * @see verifier.ast.AST#eval(verifier.ActivationRecord)
	 */
	@Override
	public Value eval(ActivationRecord environment) {
		if (_antecedentValue == null)
			_antecedentValue = _antecedent.eval(environment);

		if (_consequentValue == null)
			_consequentValue = _consequent.eval(environment);

		return _antecedentValue.execute(new AValueVisitor() {

			@Override
			public Value forTrue(True t) {
				return _consequentValue.execute(new AValueVisitor() {

					@Override
					public Value forTrue(True t) {
						return True.SINGLETON;
					}

					@Override
					public Value forFalse(False f) {
						return False.SINGLETON;
					}

					@Override
					public Value forReduction(Reduction r) {
						return new Reduction(new Impl(True.SINGLETON, r
								.getAST()));
					}

				});
			}

			@Override
			public Value forFalse(False f) {
				return True.SINGLETON;
			}

			@Override
			public Value forReduction(final Reduction outer) {
				return _consequentValue.execute(new AValueVisitor() {

					@Override
					public Value forTrue(True t) {
						return True.SINGLETON;
					}

					@Override
					public Value forFalse(False f) {
						return new Reduction(new Impl(outer.getAST(),
								False.SINGLETON));
					}

					@Override
					public Value forReduction(Reduction inner) {
						return new Reduction(new Impl(outer.getAST(), inner
								.getAST()));
					}

				});
			}

		});
	}
}
