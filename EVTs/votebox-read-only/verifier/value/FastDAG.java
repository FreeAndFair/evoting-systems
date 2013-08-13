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

import java.util.*;

/**
 * Data structure for modelling a DAG of time using Crosby's optimized
 * algorithm.
 * 
 * Note that this fails if the input data can not be divided into a number of
 * intersecting, totally-ordered timelines.
 * 
 */
public class FastDAG extends DAGValue {
	private boolean _useCache = false;
    // This holds a cache: messagePointer --> [list of successor message
    // pointers].
    private final HashMap<Expression, HashSet<Expression>> _cache;

	public class MessageProjection {
		public Integer INFINITY = Integer.MAX_VALUE;

		public MessageProjection(Expression ptr) {
			_m = ptr;
			_p = new HashMap<String, Integer>();
		}

		protected final Map<String, Integer> _p;
		protected final Expression _m;
		
		public String toString() {
			String s = "<Projection: " + _m + " --> ";
			for (String host : _p.keySet()) {
				s += host + "@" + _p.get(host) + ", ";
			}
			return s + ">";
		}

		public int get(String host) {
			if (!_p.containsKey(host))
				return INFINITY;
			return _p.get(host);
		}

		public void relax(String host, Integer newIndex) {
			if (!_p.containsKey(host) || (newIndex < _p.get(host)))
				_p.put(host, newIndex);
		}

		public void set(String host, Integer index) {
			_p.put(host, index);
		}
	}

	public class Pair<A, B> {
		private final A _a;
		private final B _b;

		public Pair(A a, B b) {
			_a = a;
			_b = b;
		}

		public A left() {
			return _a;
		}

		public B right() {
			return _b;
		}
	}

	// / P(msg, host)
	private final Map<Expression, MessageProjection> _projections;

	// / host --> (int -> ptr)
	private final Map<String, Map<Integer, Expression>> _timelines;
	
	// / inversion of the above: ptr --> (host, int)
	private final Map<Expression, Pair<String, Integer>> _ptrToHost;

	// / msg --> (ptr ...)
	private final Map<Expression, Expression> _messageToPtr;
	// private final Map<Expression, Expression> _ptrToMessage;

	// / mapping of ptr-->(listof predecessor ptrs)
	private final Map<Expression, List<Expression>> _predecessors;

	public void enableCache() { _useCache = true; }
	public void disableCache() { _useCache = false; }

	public FastDAG(Map<Expression, Expression> messageToPtrMap,
			Map<Expression, List<Expression>> predecessors,
			Map<String, Map<Integer, Expression>> hostTimelines)
	{
		_messageToPtr = messageToPtrMap;
		_predecessors = predecessors;
		_timelines = hostTimelines;
		_projections = new HashMap<Expression, MessageProjection>();

		// create the inverted index
		/*
		 * _ptrToMessage = new HashMap<Expression, Expression>(); for
		 * (Expression msg : _messageToPtr.keySet())
		 * _ptrToMessage.put(_messageToPtr.get(msg), msg);
		 */

		// create the inverted index
		_ptrToHost = new HashMap<Expression, Pair<String, Integer>>();

		for (String host : _timelines.keySet()) {
			Map<Integer, Expression> timeline = _timelines.get(host);
			for (Integer i : timeline.keySet()) {
				_ptrToHost.put(timeline.get(i), 
							   new Pair<String, Integer>(host, i));
			}
		}

		
		_cache = new HashMap<Expression, HashSet<Expression>>();
		for (Expression e : _predecessors.keySet())
			_cache.put( e, new HashSet<Expression>() );
	}

	/**
	 * Determine whether leftMessage precedes rightMessage by performing a
	 * breadth-first search for a precedence path in the DAG.
	 * 
	 * @param leftMessage
	 *            Compute if this expression precedes r.
	 * @param rightMessage
	 *            Compute if l precedes this expression.
	 * @return This method returns true in O(1) if it results in a cache hit.
	 * @throws IncorrectFormatException
	 */
	public boolean precedes(Expression leftMessage, Expression rightMessage) {
		Expression finish = _messageToPtr.get(leftMessage);
		Expression start = _messageToPtr.get(rightMessage);

//		System.out.println("precedes: searching for " + finish + " <<? " + start);

        if (finish.equals( start ))
            return false;
        if (!(_predecessors.containsKey( finish ) && _predecessors
                .containsKey( start )))
            return false;

        // Check the cache.
		if (_useCache) {
			if (_cache.get( start ).contains( finish ))
				return true;
		}

		if (! _projections.containsKey(start))
			_projections.put(start, new MessageProjection(start));

		Pair<String, Integer> finishHostIndex = _ptrToHost.get(finish);

		// Algorithm: revised Crosby with lazy precomputation
		// Start at finish at message m1 on host h1; perform a BFS for the next
		// preceding message m2 in h2, then compare sequence numbers
		// and cache projection from m1 onto h2

		// BFS work
		Queue<Expression> work = new LinkedList<Expression>();

		work.offer(start); // start at the end and work our way back
		while (work.peek() != null) {
			Expression e = work.poll();

			Pair<String, Integer> messagePosition = _ptrToHost.get(e);

			// first, let's cache the projection from the start onto whatever
			// host we happen to have found
			_projections.get(start).relax(
					messagePosition.left(), /* host */
					messagePosition.right() /* index */
			);

			if (messagePosition.left() == finishHostIndex.left()) {
//				System.out.println("precedes: found our way to target host: " 
//						+ messagePosition.left());
//				System.out.println("precedes: comparing projected position "
//						+ messagePosition.left() + "@"
//						+ messagePosition.right() + " to target position "
//						+ finishHostIndex.left() + "@"
//						+ finishHostIndex.right());
				
				// found a path to the same HOST as the target
				// now we have an opportunity to short-circuit the search and
				// look for a direct path
				boolean result = (
					/*
					 * the latest position on the target timeline that provably
					 * precedes our start
					 */
					messagePosition.right()
					
					/* is after (greater than or equal to) */
					>=
					
					/* the position on the target timeline in question */
					finishHostIndex.right()
				);
				
				// found a path. look no further.
				if (result) return true;
				
				// ok, we didn't find a path, but that doesn't mean one
				// doesn't exist ... so the BFS goes on
			} else {
				// We only continue searching along this path if we have not
				// yet hit the target timeline.  If we hit the target timeline
				// but hit it too early to satisfy "precedes", we know we can
				// only go further back from here.  
				//
				// Previously the following was not in the 'else' of the
				// target-timeline test, which was a BIG BUG that slows this
				// search way down.
				List<Expression> preds = _predecessors.get(e);

				if (preds == null) {
					System.err.println("warning: message missing from DAG: ptr="
							+ e.toString());
				} else {
					for (Expression ptr : preds) {
						if (!work.contains(ptr)) {
							work.offer(ptr);
							if (_useCache)
								// retain precedence info
								_cache.get( start ).add( ptr );
						}
					}
				}
			}
		}

//		System.out.println("precedes: RETURNING " + false);
		return false; /* incomparable in time */
	}

	/**
	 * @see verifier.value.Value#execute(verifier.value.IValueVisitor)
	 */
	public Value execute(IValueVisitor visitor) {
		return visitor.forDAG(this);
	}

	/**
	 * Lookup the number of nodes in this dag.
	 * 
	 * @return This method returns the number of nodes in this dag.
	 */
	public int size() {
		return _predecessors.size();
	}

}
