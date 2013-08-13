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

package sexpression.test;

import static org.junit.Assert.*;

import java.util.HashMap;

import org.junit.Test;

import sexpression.*;

public class PatternTest {

    // OLD
    @Test
    public void literal() throws Exception {
        ASExpression e1 = ASExpression.make( "()" );
        ASExpression r1 = ASExpression.make( "()" );
        ASExpression m1 = e1.match( r1 );
        assertNotSame( m1, NoMatch.SINGLETON );
        assertTrue( m1 instanceof ListExpression );
        assertTrue( ((ListExpression) m1).size() == 0 );

        ASExpression e2 = ASExpression.make( "foo" );
        ASExpression r2 = ASExpression.make( "foo" );
        assertNotSame( NoMatch.SINGLETON, e2.match( r2 ) );

        assertEquals( NoMatch.SINGLETON, e1.match( e2 ) );

        ASExpression e3 = new ListExpression( e2, e2, new ListExpression( e2 ) );

        assertEquals( NoMatch.SINGLETON, e1.match( e3 ) );

        assertEquals( NoMatch.SINGLETON, e3.match( e1 ) );

        assertEquals( NoMatch.SINGLETON, new ListExpression( e2 ).match( e3 ) );

        assertNotSame( NoMatch.SINGLETON, e3.match( e3 ) );
    }

    @Test
    public void test_simple_wild() throws Exception {
        ASExpression e1 = ListExpression.EMPTY;
        ASExpression e2 = StringExpression.makeString( "foo" );

        ASExpression listwc = ASExpression.make( "#list:#any" );
        ASExpression stringwc = StringWildcard.SINGLETON;

        ASExpression m1 = listwc.match( e1 );
        assertNotNull( m1 );
        assertTrue( m1 instanceof ListExpression );
        assertTrue( ((ListExpression) m1).size() == 1 );
        assertTrue( ((ListExpression) m1).get( 0 ).equals( e1 ) ); // relies on
        // correctness of test_literal

        assertEquals( NoMatch.SINGLETON, listwc.match( e2 ) );

        ASExpression m2 = stringwc.match( e2 );
        assertNotNull( m2 );
        assertTrue( m2 instanceof ListExpression );
        assertTrue( ((ListExpression) m2).size() == 1 );
        assertTrue( ((ListExpression) m2).get( 0 ).equals( e2 ) ); // relies on
        // correctness
        // of
        // test_literal

        assertEquals( NoMatch.SINGLETON, stringwc.match( e1 ) );

        assertNotNull( Wildcard.SINGLETON.match( e1 ) );
        assertNotNull( Wildcard.SINGLETON.match( e2 ) );
    }

    @Test
    public void test_deep_list_wild() throws Exception {
        ASExpression target1 = new ListExpression( StringExpression
                .makeString( "Hello" ), StringExpression.makeString( "World" ) );

        ASExpression p1 = ASExpression.make( "#list:#any" );
        ASExpression m1 = p1.match( target1 );
        assertNotNull( m1 );

        ASExpression p2 = new ListExpression( StringWildcard.SINGLETON,
                StringWildcard.SINGLETON );
        ASExpression m2 = p2.match( target1 );
        assertNotNull( m2 );

        ASExpression p3 = new ListExpression( StringWildcard.SINGLETON,
                StringExpression.makeString( "World" ) );
        ASExpression m3 = p3.match( target1 );
        assertNotNull( m3 );

        ASExpression p4 = new ListExpression( StringExpression
                .makeString( "Hello" ), StringWildcard.SINGLETON );
        ASExpression m4 = p4.match( target1 );
        assertNotNull( m4 );

        ASExpression p5 = new ListExpression( StringWildcard.SINGLETON,
                StringWildcard.SINGLETON, StringWildcard.SINGLETON );
        ASExpression m5 = p5.match( target1 );
        assertTrue( m5 == NoMatch.SINGLETON );

        ASExpression p6 = new ListExpression( StringExpression
                .makeString( "Hello" ), StringWildcard.SINGLETON,
                StringExpression.makeString( "World" ) );
        ASExpression m6 = p6.match( target1 );
        assertTrue( m6 == NoMatch.SINGLETON );

        ASExpression p7 = new ListExpression( StringExpression
                .makeString( "Hello" ) );
        ASExpression m7 = p7.match( target1 );
        assertTrue( m7 == NoMatch.SINGLETON );
    }

    // ADDED 9/18/2007
    @Test
    public void test_fancy_wildcards() {
        assertTrue( test( "foo", "foo" ) );
        assertTrue( test( "bar", "bar" ) );
        assertTrue( test( "()", "()" ) );
        assertTrue( test( "(foo)", "(foo)" ) );
        assertTrue( test( "#nomatch", "#nomatch" ) );
        assertTrue( test( "#nothing", "#nothing" ) );

        assertFalse( test( "(foo)", "(bar)" ) );
        assertFalse( test( "()", "(bar)" ) );
        assertFalse( test( "foo", "bar" ) );
        assertFalse( test( "(bar)", "()" ) );

        assertTrue( test( "#string", "foo" ) );
        assertTrue( test( "#string", "bar" ) );

        assertFalse( test( "#string", "()" ) );
        assertFalse( test( "#string", "(asdf)" ) );
        assertFalse( test( "#string", "#string" ) );

        assertTrue( test( "#wildcard", "#wildcard" ) );
        assertTrue( test( "#wildcard", "#string" ) );
        assertTrue( test( "#wildcard", "#any" ) );
        assertTrue( test( "#wildcard", "#list:#any" ) );
        assertTrue( test( "#wildcard", "#list:((#string))" ) );

        assertFalse( test( "#wildcard", "()" ) );
        assertFalse( test( "#wildcard", "(boo hoo)" ) );
        assertFalse( test( "#wildcard", "asdfa" ) );

        assertTrue( test( "#list:#any", "(bar)" ) );
        assertTrue( test( "#list:#any", "(bar (bar))" ) );
        assertTrue( test( "(bar #list:#any)", "(bar (bar))" ) );
        assertTrue( test( "(bar #list:bar)", "(bar (bar))" ) );
        assertTrue( test( "#list:#list:#string",
            "((bar bar foo) (foo) (foo bar baz quux) ())" ) );
        assertTrue( test( "#list:#wildcard", "(#wildcard #string #list:any)" ) );
        assertTrue( test( "#list:#wildcard", "()" ) );

        assertFalse( test( "#list:#any", "bar" ) );
        assertFalse( test( "#list:#string", "(())" ) );
        assertFalse( test( "#list:#string", "bar" ) );
        assertFalse( test( "#list:#string", "#list:#string" ) );
        assertFalse( test( "#list:#list:#string",
            "((bar bar foo) foo (foo bar baz quux) ())" ) );
        assertFalse( test( "#list:#wildcard", "(false)" ) );
    }

    private boolean test(String l, String r) {
        ASExpression le = ASExpression.make( l );
        ASExpression re = ASExpression.make( r );
        assertEquals( le.toString(), l );
        assertEquals( re.toString(), r );
        return le.match( re ) != NoMatch.SINGLETON
                && le.namedMatch( re ) != NamedNoMatch.SINGLETON;
    }

    @Test
    public void named() {
        HashMap<String, ASExpression> mp;

        mp = match( "%kyle:#string", "foo" );
        assertEquals( "foo", mp.get( "kyle" ).toString() );

        mp = match( "(%kyle:#string #any)", "(foo any)" );
        assertEquals( "foo", mp.get( "kyle" ).toString() );
        assertNull( mp.get( "any" ) );

        mp = match( "%kyle:#string", "foo" );
        assertEquals( "foo", mp.get( "kyle" ).toString() );

        mp = match( "(%one:#string %two:#list:#string)", "(foo (bar))" );
        assertEquals( "foo", mp.get( "one" ).toString() );
        assertEquals( "(bar)", mp.get( "two" ).toString() );

        mp = match( "(%one:#string (%two:#string %three:#wildcard))",
            "(foo (bar #string))" );
        assertEquals( "foo", mp.get( "one" ).toString() );
        assertEquals( "bar", mp.get( "two" ).toString() );
        assertEquals( "#string", mp.get( "three" ).toString() );
    }

    private HashMap<String, ASExpression> match(String l, String r) {
        return ASExpression.make( l ).namedMatch( ASExpression.make( r ) );
    }

    @Test
    public void match_return_val() {
        assertEquals( "((x) 1)", ASExpression.make(
            "(lambda #list:#string #any)" ).match(
            ASExpression.make( "(lambda (x) 1)" ) ).toString() );
    }
}
