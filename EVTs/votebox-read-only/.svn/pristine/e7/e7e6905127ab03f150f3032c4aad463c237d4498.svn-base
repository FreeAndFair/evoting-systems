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

import java.util.LinkedList;
import java.util.Queue;

/**
 * Use a job pool to compute a task in parallel. The parallelism comes from
 * tasks which are dependent on any task given. (Any dependent tasks can be
 * computed in parallel.)
 * 
 * @author kyle
 * 
 */
public class Pool {

	private final int _threads;
	private final Queue<Task> _ready;
	private volatile boolean _running = false;

	/**
	 * @param threads
	 *            Use this number of threads in parallel to execute tasks.
	 */
	public Pool(int threads) {
		_threads = threads;
		_ready = new LinkedList<Task>();
	}

	/**
	 * Start the threads.
	 */
	public synchronized void start() {
		if (_running)
			return;
		_running = true;
		for (int lcv = 0; lcv < _threads; lcv++) {
			new Thread(new Runnable() {

				public void run() {
					try {
						thread();
					} catch (Exception e) {
						e.printStackTrace();
						System.exit(1);
					}
				}
			}).start();
		}
	}

	/**
	 * Stop the threads.
	 */
	public synchronized void stop() {
		_running = false;
		notifyAll();
	}

	/**
	 * @param task
	 *            Schedule this task to run.
	 */
	public synchronized void run(Task task) {
		_ready.add(task);
		notify();
	}

	/**
	 * Dequeue a task. If no task is available, this call will block until one
	 * becomes available.
	 * 
	 * @return This method returns the dequeued task.
	 */
	public synchronized Task getJob() {
		while (_running && _ready.size() == 0)
			try {
				wait();
			} catch (InterruptedException e) {
				throw new RuntimeException(e);
			}
		return _ready.poll();

	}

	/**
	 * @return This method returns true if the pool is running
	 */
	public boolean running() {
		return _running;
	}

	private void thread() {
		while (_running) {
			Task job = getJob();
			if (job != null)
				try {
					job.run();
				} catch (RuntimeException e) {
					stop();
				}

		}
	}
}
