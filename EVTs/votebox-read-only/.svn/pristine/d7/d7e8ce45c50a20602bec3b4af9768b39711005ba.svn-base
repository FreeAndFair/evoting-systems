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

import sexpression.*;
import verifier.*;
import verifier.ast.*;
import verifier.value.*;

/**
 * A local task performs the computation on the local machine, never requiring
 * serialization.
 * 
 * @author kyle
 * 
 */
public class LocalTask extends Task {

	private final Future _future;

	/**
	 * @param future
	 *            Realize this future with the result of the task.
	 * @param ast
	 *            Evaluate this ast.
	 * @param environment
	 *            Evaluate the ast in this environment.
	 */
	public LocalTask(Future future, AST ast, ActivationRecord environment) {
		super(null, ast, environment);
		_future = future;
	}

	/**
	 * @see verifier.task.Task#run()
	 */
	@Override
	public void run() {
		_future.realize(_ast.eval(_environment));
	}

	/**
	 * @see verifier.task.Task#toASE()
	 */
	@Override
	public ASExpression toASE() {
		throw new RuntimeException("Cannot serialize a local task");
	}

}
