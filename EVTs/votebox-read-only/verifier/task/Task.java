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

package verifier.task;

import java.io.IOException;
import java.io.OutputStream;

import sexpression.*;
import verifier.*;
import verifier.value.*;
import verifier.ast.*;

/**
 * Tasks represent a computation job, the result of which will be realized in
 * some future instance. Tasks are abstract because they exist in two places: on
 * the compute node, and on the controller.
 * 
 * @author derrley
 * 
 */
public class Task {

	public final Long _future;
	protected final AST _ast;
	protected final ActivationRecord _environment;

	private OutputStream _outbound;

	/**
	 * @param future
	 *            Construct a task whose results will get realized in this
	 *            future.
	 * @param ast
	 *            Construct a task which evaluates this AST.
	 * @param environment
	 *            Construct a task which does an evaluation in this environment.
	 */
	public Task(Future future, AST ast, ActivationRecord environment) {
		if (future == null)
			_future = null;
		else
			_future = future._id;
		_ast = ast;
		_environment = environment;
	}

	/**
	 * @param os
	 *            When the task is finished, the result of the task will be
	 *            written to this stream.
	 */
	public void setOutbound(OutputStream os) {
		_outbound = os;
	}

	/**
	 * Construct a task object from its wire format.
	 * 
	 * @param ase
	 *            This is the s-expression heard over the wire.
	 */
	public Task(ASExpression ase) {
		ListExpression list = (ListExpression) ase;
		_future = Long.parseLong(list.get(0).toString());
		_ast = ASTParser.PARSER.parse(list.get(1));
		_environment = new ActivationRecord(list.get(2));
	}

	/**
	 * @return This method returns the s-expression format for the target task.
	 */
	public ASExpression toASE() {
		return new ListExpression(
				StringExpression.make(Long.toString(_future)), _ast.toASE(),
				_environment.toASE());
	}

	public void run() {
		Value v = _ast.eval(_environment);
		try {
			_outbound.write(new ListExpression(StringExpression.make(Long
					.toString(_future)), v.toASE()).toVerbatim());
			_outbound.flush();
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
	}
}
