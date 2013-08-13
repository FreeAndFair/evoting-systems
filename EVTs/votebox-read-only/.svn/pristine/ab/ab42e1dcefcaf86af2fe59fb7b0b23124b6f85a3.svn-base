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

package votebox.auditoriumverifierplugins;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import sexpression.ASExpression;
import sexpression.ListExpression;
import sexpression.ListWildcard;
import sexpression.NoMatch;
import sexpression.StringExpression;
import sexpression.StringWildcard;
import sexpression.Wildcard;
import verifier.FormatException;
import verifier.value.*;
import auditorium.IncorrectFormatException;
import auditorium.Message;
import auditorium.MessagePointer;



public class FastDAGBuilder extends DagBuilder {

    /*
     * Matching against this pattern should yield the following: [0]: cert [1]:
     * signer id [2]: sigdata [3]: list of pointers that preceed [4]: data
     */
    private static final ASExpression PATTERN = new ListExpression(
            StringExpression.makeString( "signed-message" ),
            Wildcard.SINGLETON, new ListExpression( StringExpression
                    .makeString( "signature" ), StringWildcard.SINGLETON,
                    StringWildcard.SINGLETON, new ListExpression(
                            StringExpression.makeString( "succeeds" ),
                            new ListWildcard( MessagePointer.PATTERN ),
                            Wildcard.SINGLETON ) ) );

    /// mapping of ptr-->(listof predecessor ptrs)  
    private HashMap<Expression, List<Expression>> _predecessors;
    /// mapping of message-->its own ptr
    private HashMap<Expression, Expression> _msgToPtr;
    
    private Map<String, Map<Integer, Expression>> _timelines;
    
    public FastDAGBuilder() {
        _predecessors = new HashMap<Expression, List<Expression>>();
        _msgToPtr = new HashMap<Expression, Expression>();
        _timelines = new HashMap<String, Map<Integer, Expression>>();
    }

	
    public void add(Message message) throws FormatException {
        try {
        	MessagePointer msgPtr = new MessagePointer(message);
        	Expression ptr = new Expression(msgPtr.toASE());
        	Expression expr = new Expression( message.toASE() );
            
        	// store ptr-->message mapping in DAG
            _msgToPtr.put( expr, ptr );
            
            // store timeline index
            if (! _timelines.containsKey(msgPtr.getNodeId()))
            	_timelines.put(msgPtr.getNodeId(), 
            				   new HashMap<Integer, Expression>());
            _timelines.get(msgPtr.getNodeId()).put(
            		new Integer(msgPtr.getNumber()),
            		ptr);

            ASExpression matchresult = PATTERN.match( message.getDatum() );
            if (matchresult == NoMatch.SINGLETON)
                throw new FormatException( message.getDatum(), new Exception(
                        "didn't match pattern for an Auditorium message: "
                		+ PATTERN ) );
            ListExpression matchlist = (ListExpression) matchresult;

            ArrayList<Expression> ptrlst = new ArrayList<Expression>();
            for (ASExpression ptrexp : (ListExpression) matchlist.get( 3 )) {
                ptrlst.add( new Expression( 
                		new MessagePointer( ptrexp ).toASE() ) );
            }
            
            _predecessors.put( ptr, ptrlst );
        }
        catch (IncorrectFormatException e) {
            throw new FormatException( message.getDatum(), e );
        }
   }

    public DAGValue toDAG() {
    	return new FastDAG(_msgToPtr,
    			_predecessors,
    			_timelines);
    }
}
