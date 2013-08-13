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

package verifier.value;

import java.lang.ref.WeakReference;
import java.util.HashMap;

import sexpression.*;

/**
 * A future represents a value being computed in parallel by another worker
 * thread. If a future's visitor execute method is called before this value is
 * computed, the calling thread will block until the value is realized.
 * 
 * @author derrley
 * 
 */
public class Future extends Value {

	public static long ID = 0;

	private static final HashMap<Long, WeakReference<Future>> TABLE = new HashMap<Long, WeakReference<Future>>();

	/**
	 * Get a reference to a particular future.
	 * 
	 * @param id
	 *            Get a reference to the future with this ID.
	 * @return This method returns the reference to the future with this ID.
	 */
	public static Future fromID(long id) {
		synchronized (TABLE) {
			if (!TABLE.containsKey(id))
				throw new RuntimeException("future not mapped");
			WeakReference<Future> w = TABLE.get(id);
			if (w.get() == null)
				throw new RuntimeException("future has been collected");
			return w.get();
		}
	}

	/**
	 * @param f
	 *            Register this future in the table so that it can be found and
	 *            realized by remote hosts.
	 */
	public static void registerFuture(Future f) {
		synchronized (TABLE) {
			TABLE.put(f._id, new WeakReference<Future>(f));
		}
	}

	public Future() {
		super(true);
		_id = ID;
		ID++;
	}

	public final long _id;

	private Value _value;

	/**
	 * Realize the value for this future.
	 * 
	 * @param v
	 *            Make the target future represent this value.
	 */
	public synchronized void realize(Value v) {
		_value = v;
		notifyAll();
	}

	/**
	 * @see verifier.value.Value#execute(verifier.value.IValueVisitor)
	 */
	@Override
	public synchronized Value execute(IValueVisitor visitor) {
		while (_value == null)
			try {
				wait();
			} catch (InterruptedException e) {
				throw new RuntimeException(e);
			}
		return _value.execute(visitor);
	}

	/**
	 * @see verifier.value.Value#toASE()
	 */
	@Override
	public ASExpression toASE() {
		throw new RuntimeException("tried to serialize a future");
	}
}
