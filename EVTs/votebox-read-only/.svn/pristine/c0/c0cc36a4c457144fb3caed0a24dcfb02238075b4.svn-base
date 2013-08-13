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

import java.io.IOException;
import java.io.OutputStream;

import sexpression.ASExpression;
import sexpression.ListExpression;
import verifier.*;
import verifier.task.*;
import verifier.value.*;

public class Spawn extends AST {

	public static final ASTFactory FACTORY = new ASTFactory() {

		@Override
		public String getName() {
			return "spawn";
		}

		@Override
		public String getPattern() {
			return "(spawn #any)";
		}

		@Override
		public AST make(ASExpression from, ListExpression matchresult,
				ASTParser parser) {
			return new Spawn(parser.parse(matchresult.get(0)));
		}
	};

	private final AST _body;

	private Spawn(AST body) {
		super(null);
		_body = body;
	}

	@Override
	public ASExpression toASE() {
		throw new RuntimeException("Nested spawn not supported");
	}

	/**
	 * @see verifier.ast.AST#eval(verifier.ActivationRecord)
	 */
	@Override
	public Value eval(ActivationRecord environment) {
		Future f = new Future();
		Future.registerFuture(f);
		try {
			OutputStream os = Controller.SINGLETON.getOutbound();
			os.write(new Task(f, _body, environment).toASE().toVerbatim());
			os.flush();
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
		return f;
	}

}
