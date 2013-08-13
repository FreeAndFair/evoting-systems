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

package verifier.value.test;

import java.util.ArrayList;
import java.util.HashMap;

import org.junit.*;

import static org.junit.Assert.*;

import verifier.value.*;

import sexpression.*;

/**
 * Test the DAG value's operations.
 * 
 * XXX: this test is completely broken now that the LHS and RHS must be parsed
 * to find out what their pointers are. --dsandler
 * 
 * @author kyle
 * 
 */
public class DagTest {

    private final HashMap<Expression, ArrayList<Expression>> _struct = new HashMap<Expression, ArrayList<Expression>>();
    private final HashMap<Expression, Expression> _pointers = new HashMap<Expression, Expression>();
    private ExplicitDAG _dag;

    private final Expression[] _data = {
            new Expression( StringExpression.makeString( "ZERO" ) ),
            new Expression( StringExpression.makeString( "ONE" ) ),
            new Expression( StringExpression.makeString( "TWO" ) ),
            new Expression( StringExpression.makeString( "THREE" ) ),
            new Expression( StringExpression.makeString( "FOUR" ) ),
            new Expression( StringExpression.makeString( "FIVE" ) ),
            new Expression( StringExpression.makeString( "SIX" ) ),
            new Expression( StringExpression.makeString( "SEVEN" ) ),
            new Expression( StringExpression.makeString( "EIGHT" ) )
    };

    @Before
    public void setup() {
        _struct.clear();
        _pointers.clear();
        _pointers.put( _data[0], _data[0] );
        _pointers.put( _data[1], _data[1] );
        _pointers.put( _data[2], _data[2] );
        _pointers.put( _data[3], _data[3] );
        _pointers.put( _data[4], _data[4] );
        _pointers.put( _data[5], _data[5] );
        _pointers.put( _data[6], _data[6] );
        _pointers.put( _data[7], _data[7] );
        _pointers.put( _data[8], _data[8] );
    }

    public void construct() {
        _dag = new ExplicitDAG( _pointers, _pointers, _struct );
    }

    public void map(Expression from, Expression to) {
        ArrayList<Expression> lst = null;
        if (_struct.containsKey( from ))
            lst = _struct.get( from );
        else {
            lst = new ArrayList<Expression>();
            _struct.put( from, lst );
        }

        lst.add( to );
    }

    public void maptonull(Expression exp) {
        _struct.put( exp, new ArrayList<Expression>() );
    }

    @Test
    public void empty() {
        construct();
        assertFalse( _dag.precedes( _data[0], _data[0] ) );
        assertFalse( _dag.precedes( _data[1], _data[1] ) );
        assertFalse( _dag.precedes( _data[0], _data[1] ) );
    }

    @Test
    public void one_elt() {
        maptonull( _data[0] );

        construct();

        assertFalse( _dag.precedes( _data[0], _data[0] ) );
        assertFalse( _dag.precedes( _data[1], _data[1] ) );
        assertFalse( _dag.precedes( _data[0], _data[1] ) );
    }

    @Test
    public void two_elt_same() {
        map( _data[0], _data[0] );

        construct();

        assertFalse( _dag.precedes( _data[0], _data[0] ) );
    }

    @Test
    public void two_elt() {
        maptonull( _data[0] );
        map( _data[1], _data[0] );

        construct();

        assertFalse( _dag.precedes( _data[0], _data[0] ) );
        assertFalse( _dag.precedes( _data[1], _data[1] ) );
        assertTrue( _dag.precedes( _data[0], _data[1] ) );
    }

   /* @Test
    public void three_elt() {
        maptonull( _data[0] );
        map( _data[1], _data[0] );
        map( _data[2], _data[0] );

        construct();

        assertFalse( _dag.precedes( _data[0], _data[1] ) );
        assertFalse( _dag.precedes( _data[0], _data[2] ) );
        assertTrue( _dag.precedes( _data[0], _data[1] ) );
        assertTrue( _dag.precedes( _data[0], _data[2] ) );
        assertFalse( _dag.precedes( _data[1], _data[2] ) );
        assertFalse( _dag.precedes( _data[2], _data[1] ) );
    }*/

    // ........3 - 7 - 8
    // ....1 -[
    // ........4
    // 0-[
    // ........5
    // ....2 -[
    // ........6
    /*@Test
    public void eight_elt() {
        maptonull( _data[0] );

        map( _data[1], _data[0] );
        map( _data[2], _data[0] );

        map( _data[3], _data[1] );
        map( _data[4], _data[1] );

        map( _data[5], _data[2] );
        map( _data[6], _data[2] );

        map( _data[7], _data[3] );

        map( _data[8], _data[7] );

        construct();

        assertFalse( _dag.precedes( _data[0], _data[0] ) );
        assertFalse( _dag.precedes( _data[0], _data[1] ) );
        assertFalse( _dag.precedes( _data[0], _data[2] ) );
        assertFalse( _dag.precedes( _data[0], _data[3] ) );
        assertFalse( _dag.precedes( _data[0], _data[4] ) );
        assertFalse( _dag.precedes( _data[0], _data[5] ) );
        assertFalse( _dag.precedes( _data[0], _data[6] ) );
        assertFalse( _dag.precedes( _data[0], _data[7] ) );
        assertFalse( _dag.precedes( _data[0], _data[8] ) );

        assertTrue( _dag.precedes( _data[0], _data[1] ) );
        assertFalse( _dag.precedes( _data[1], _data[1] ) );
        assertFalse( _dag.precedes( _data[1], _data[2] ) );
        assertFalse( _dag.precedes( _data[1], _data[3] ) );
        assertFalse( _dag.precedes( _data[1], _data[4] ) );
        assertFalse( _dag.precedes( _data[1], _data[5] ) );
        assertFalse( _dag.precedes( _data[1], _data[6] ) );
        assertFalse( _dag.precedes( _data[1], _data[7] ) );
        assertFalse( _dag.precedes( _data[1], _data[8] ) );

        assertTrue( _dag.precedes( _data[0], _data[2] ) );
        assertFalse( _dag.precedes( _data[2], _data[1] ) );
        assertFalse( _dag.precedes( _data[2], _data[2] ) );
        assertFalse( _dag.precedes( _data[2], _data[3] ) );
        assertFalse( _dag.precedes( _data[2], _data[4] ) );
        assertFalse( _dag.precedes( _data[2], _data[5] ) );
        assertFalse( _dag.precedes( _data[2], _data[6] ) );
        assertFalse( _dag.precedes( _data[2], _data[7] ) );
        assertFalse( _dag.precedes( _data[2], _data[8] ) );

        assertTrue( _dag.precedes( _data[0], _data[3] ) );
        assertTrue( _dag.precedes( _data[1], _data[3] ) );
        assertFalse( _dag.precedes( _data[3], _data[2] ) );
        assertFalse( _dag.precedes( _data[3], _data[3] ) );
        assertFalse( _dag.precedes( _data[3], _data[4] ) );
        assertFalse( _dag.precedes( _data[3], _data[5] ) );
        assertFalse( _dag.precedes( _data[3], _data[6] ) );
        assertFalse( _dag.precedes( _data[3], _data[7] ) );
        assertFalse( _dag.precedes( _data[3], _data[8] ) );

        assertTrue( _dag.precedes( _data[0], _data[4] ) );
        assertTrue( _dag.precedes( _data[1], _data[4] ) );
        assertFalse( _dag.precedes( _data[4], _data[2] ) );
        assertFalse( _dag.precedes( _data[4], _data[3] ) );
        assertFalse( _dag.precedes( _data[4], _data[4] ) );
        assertFalse( _dag.precedes( _data[4], _data[5] ) );
        assertFalse( _dag.precedes( _data[4], _data[6] ) );
        assertFalse( _dag.precedes( _data[4], _data[7] ) );
        assertFalse( _dag.precedes( _data[4], _data[8] ) );

        assertTrue( _dag.precedes( _data[0], _data[5] ) );
        assertFalse( _dag.precedes( _data[5], _data[1] ) );
        assertTrue( _dag.precedes( _data[2], _data[5] ) );
        assertFalse( _dag.precedes( _data[5], _data[3] ) );
        assertFalse( _dag.precedes( _data[5], _data[4] ) );
        assertFalse( _dag.precedes( _data[5], _data[5] ) );
        assertFalse( _dag.precedes( _data[5], _data[6] ) );
        assertFalse( _dag.precedes( _data[5], _data[7] ) );
        assertFalse( _dag.precedes( _data[5], _data[8] ) );

        assertTrue( _dag.precedes( _data[0], _data[6] ) );
        assertFalse( _dag.precedes( _data[6], _data[1] ) );
        assertTrue( _dag.precedes( _data[2], _data[6] ) );
        assertFalse( _dag.precedes( _data[6], _data[3] ) );
        assertFalse( _dag.precedes( _data[6], _data[4] ) );
        assertFalse( _dag.precedes( _data[6], _data[5] ) );
        assertFalse( _dag.precedes( _data[6], _data[6] ) );
        assertFalse( _dag.precedes( _data[6], _data[7] ) );
        assertFalse( _dag.precedes( _data[6], _data[8] ) );

        assertTrue( _dag.precedes( _data[0], _data[7] ) );
        assertTrue( _dag.precedes( _data[1], _data[7] ) );
        assertFalse( _dag.precedes( _data[7], _data[2] ) );
        assertTrue( _dag.precedes( _data[3], _data[7] ) );
        assertFalse( _dag.precedes( _data[7], _data[4] ) );
        assertFalse( _dag.precedes( _data[7], _data[5] ) );
        assertFalse( _dag.precedes( _data[7], _data[6] ) );
        assertFalse( _dag.precedes( _data[7], _data[7] ) );
        assertFalse( _dag.precedes( _data[7], _data[8] ) );

        assertTrue( _dag.precedes( _data[0], _data[8] ) );
        assertTrue( _dag.precedes( _data[1], _data[8] ) );
        assertFalse( _dag.precedes( _data[8], _data[2] ) );
        assertTrue( _dag.precedes( _data[3], _data[8] ) );
        assertFalse( _dag.precedes( _data[8], _data[4] ) );
        assertFalse( _dag.precedes( _data[8], _data[5] ) );
        assertFalse( _dag.precedes( _data[8], _data[6] ) );
        assertTrue( _dag.precedes( _data[7], _data[8] ) );
        assertFalse( _dag.precedes( _data[8], _data[8] ) );
    }*/
}
