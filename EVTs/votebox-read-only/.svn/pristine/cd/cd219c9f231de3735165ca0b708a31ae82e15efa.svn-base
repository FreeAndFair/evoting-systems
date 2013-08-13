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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;

/**
 * Data structure for modelling a DAG of time explicitly as a graph.
 *
 * Distributed logging messages make up a non-linear timeline. Because of the
 * possibility that two messages can be sent at the same time, or because the
 * possibility of a non-fully connected graph of nodes, not every message can be
 * claimed to exist either before or after every other message. This means that,
 * rather than the timeline being a "list" of messages, the timeline is a
 * "directed, acyclic graph" (or DAG) of messages. The job of this data
 * structure is to hold said DAG information.<br>
 * <br>
 * Information gathered during a DAG traversal is cached (memoized) for later
 * possible use.<br>
 * <br>
 * The dag storage format is not tied to a particular log format. Any
 * application specific log file which encodes precedence between log entries
 * can be expressed using one of these dags. The only constraint we place on the
 * format is that there be a canonical, unique "pointer" expression for every
 * expression in the log. This allows us to specify the DAG using two mappings:
 * (1) one which maps every pointer expression to the expression to which it
 * points, and (2) one which maps every expression to a list of pointer
 * expressions, each of which point to an expression provably succeeding the key
 * expression in the DAG. We simply check for equality between pointer
 * expressions in (2) and in (1) (essentially "connecting the dots") to
 * reconstruct the DAG.
 * 
 * @author kyle
 * 
 */
public class ExplicitDAG extends DAGValue {
	private boolean _useCache = false;

    // maps every pointer expression to the expression to which it points
    @SuppressWarnings("unused")
	private final Map<Expression, Expression> _ptrToMessage;
    // maps every message expression to its own pointer (so we don't have to
    // compute that here; it is application-specific)
    private final Map<Expression, Expression> _messageToPtr;

    // maps every expression pointer to a list of pointers to messages that
    // precede it.
    private final Map<Expression, ArrayList<Expression>> _predecessors;

    // This holds a cache: 
    // messagePointer --> [list of predecessor messagePointers].
    private final HashMap<Expression, HashSet<Expression>> _cache;
    // If an expression is in this set, you can assume all the dag information
    // is cached in _cache.
    private final HashSet<Expression> _completelyCached;

	public void enableCache() { _useCache = true; }
	public void disableCache() { _useCache = false; }

    /*}
     * Construct a dag out of a set of auditorium messages.
     * 
     * @param dag
     *            Every expression in the dag should be mapped to *all* the
     *            expressions that *succeed* it.
     */
    public ExplicitDAG(Map<Expression, Expression> pointerToMessageMap,
            Map<Expression, Expression> messageToPointerMap,
            Map<Expression, ArrayList<Expression>> predecessorGraph)
    {
        _ptrToMessage = pointerToMessageMap;
        _messageToPtr = messageToPointerMap;
        _predecessors = predecessorGraph;
        _cache = new HashMap<Expression, HashSet<Expression>>();
        _completelyCached = new HashSet<Expression>();

        initCache();
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
        Expression finish = _messageToPtr.get( leftMessage );
        Expression start = _messageToPtr.get( rightMessage );

        // Bugout.msg("precedes: searching for " + finish + " <<? " + start);

        if (finish.equals( start ))
            return false;
        if (!(_predecessors.containsKey( finish ) && _predecessors
                .containsKey( start )))
            return false;

        // Check the cache.
		if (_useCache) {
			if (_cache.get( start ).contains( finish ))
				return true;
			if (_completelyCached.contains( start ))
				return false;
		}

        // If we can't use the cache, do BFS.
        Queue<Expression> q = new LinkedList<Expression>();

        q.offer( start ); // start at the end and work our way back
        while (q.peek() != null) {
            Expression e = q.poll();
            // Bugout.msg("precedes: considering " + e);
            if (e.equals( finish )) {
                // found a path.
                return true;
            }

            ArrayList<Expression> preds = _predecessors.get( e );

            if (preds == null) {
                // this message is not in the DAG
                System.err.println( "warning: message missing from DAG: ptr="
                        + e.toString() );
            }
            else {
                for (Expression ptr : preds) {
                    if (!q.contains( ptr )) {
                        q.offer( ptr );
                        // cache that this message precedes l
                        if (_useCache)
                        	_cache.get( start ).add( ptr );
                    }
                }
            }
        }

        _completelyCached.add( start ); // exhausted the predecessor list
        // XXX: the above is fragile if used incrementally, because a new
        // ancestor (distant predecessor) previously missing from the log might
        // appear
        return false;
    }

    /**
     * @see verifier.value.Value#execute(verifier.value.IValueVisitor)
     */
    public Value execute(IValueVisitor visitor) {
        return visitor.forDAG( this );
    }

    /**
     * Lookup the number of nodes in this dag.
     * 
     * @return This method returns the number of nodes in this dag.
     */
    public int size() {
        return _predecessors.size();
    }

    private void initCache() {
        for (Expression e : _predecessors.keySet())
            _cache.put( e, new HashSet<Expression>() );
    }

}
