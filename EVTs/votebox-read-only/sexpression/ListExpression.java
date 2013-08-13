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

package sexpression;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;

/**
 * An ListExpression is an SExpression. In particular, it is a list of simpler
 * SExpressions, which, themselves, can be either other lists, strings,
 * wildcards, or the special singletons "nothing" and "nomatch."
 * 
 * @author Kyle
 * 
 */
public class ListExpression extends ASExpression implements
        Iterable<ASExpression> {

    /**
     * This represents an empty list.
     */
    public static final ListExpression EMPTY = new ListExpression();

    private ASExpression[] _list;

    private ListExpression() {
        _list = new ASExpression[0];
    }

    /**
     * for efficiency reasons, we allow users of the library to get a reference
     * to the list. DO NOT MODIFY IT! Expressions are assumed to be immutable,
     * therefore hashes and other computed values on them are only computed
     * once. If you modify this array, it might make these values inconsistent.
     * 
     * @return This method returns the actual array that this expression is
     *         based on.
     */
    public ASExpression[] getArray() {
        return _list;
    }

    /**
     * @param list
     *            This list of type ASExpression is the list that will represent
     *            this SExpressionList.
     */
    public ListExpression(List<ASExpression> list) {
        _list = list.toArray( new ASExpression[0] );
    }

    /**
     * This is a constructor for SExpressionList.
     * 
     * @param elements
     *            This is a varargs list of elements that are intended to be the
     *            elements of the list which this SExpressionList represents.
     */
    public ListExpression(ASExpression... elements) {
        _list = elements;
    }

    /**
     * Call this method to construct an S-Expression list (elt1, elt2, ...)
     * where the elements are strings (converted to ByteStringExpression)
     * 
     * @param elts
     *            This set of strings contains the elements that make up the
     *            elements of the tuple.
     * @return This method returns an S-Expression which represents a tuple
     *         containing the provided elements.
     */
    public ListExpression(String... elts) {
        ASExpression[] list = new ASExpression[elts.length];
        _list = list;
        for (int lcv = 0; lcv < elts.length; lcv++)
            _list[lcv] = StringExpression.makeString( elts[lcv] );
    }

    /**
     * @see sexpression.ASExpression#toStringHelp()
     */
    @Override
    public StringBuffer toStringHelp() {
        StringBuffer buffer = new StringBuffer();
        buffer.append( "(" );
        for (ASExpression ase : _list) {
            if (buffer.length() > 1)
                buffer.append( " " );
            buffer.append( ase.toStringHelp() );
        }
        buffer.append( ")" );
        return buffer;
    }

    /**
     * @see sexpression.ASExpression#toVerbatim()
     */
    @Override
    public ByteArrayBuffer toVerbatimHelp() {
        ByteArrayBuffer buf = new ByteArrayBuffer();
        buf.append( (byte) '(' );
        for (ASExpression ase : _list) {
            buf.append( ase.toVerbatimHelp() );
        }
        buf.append( (byte) ')' );
        return buf;
    }

    /**
     * @see sexpression.ASExpression#match(sexpression.ASExpression)
     */
    @Override
    public ASExpression match(ASExpression target) {
        if (!(target instanceof ListExpression))
            return NoMatch.SINGLETON;
        ASExpression[] targetlist = ((ListExpression) target)._list;
        if (targetlist.length != _list.length)
            return NoMatch.SINGLETON;

        ASExpression thiselt, targetelt;
        ArrayList<ASExpression> matchList = new ArrayList<ASExpression>();
        for (int lcv = 0; lcv < _list.length; lcv++) {
            thiselt = _list[lcv];
            targetelt = targetlist[lcv];

            ASExpression result = thiselt.match( targetelt );
            if (result == NoMatch.SINGLETON)
                return NoMatch.SINGLETON;
            else
                for (ASExpression ase : (ListExpression) result)
                    matchList.add( ase );

        }

        ListExpression ret = new ListExpression( matchList );
        return ret;
    }

    /**
     * @see sexpression.ASExpression#namedMatch(sexpression.ASExpression)
     */
    @Override
    public HashMap<String, ASExpression> namedMatch(ASExpression target) {
        if (!(target instanceof ListExpression))
            return NamedNoMatch.SINGLETON;
        ASExpression[] targetlist = ((ListExpression) target)._list;
        if (targetlist.length != _list.length)
            return NamedNoMatch.SINGLETON;

        ASExpression thiselt, targetelt;
        HashMap<String, ASExpression> matchList = new HashMap<String, ASExpression>();
        for (int lcv = 0; lcv < _list.length; lcv++) {
            thiselt = _list[lcv];
            targetelt = targetlist[lcv];

            HashMap<String, ASExpression> result = thiselt
                    .namedMatch( targetelt );
            if (result == NamedNoMatch.SINGLETON)
                return NamedNoMatch.SINGLETON;
            else
                matchList.putAll( result );
        }

        return matchList;
    }

    /**
     * The iterator for an SExpressionList is simply the iterator of its wrapped
     * arraylist.
     * 
     * @see java.lang.Iterable#iterator()
     */
    public Iterator<ASExpression> iterator() {
        return new Iterator<ASExpression>() {

            int pos = 0;

            public boolean hasNext() {
                return pos < _list.length;
            }

            public ASExpression next() {
                ASExpression retval = _list[pos];
                pos++;
                return retval;
            }

            public void remove() {
                throw new RuntimeException( "Removal not supported" );
            }
        };
    }

    /**
     * Call this method to get the number of elements that are in this list.
     * 
     * @return This method returns the number of elements that are in this list.
     */
    public int size() {
        return _list.length;
    }

    /**
     * Call this method to get a specific element in this list.
     * 
     * @param index
     *            This is the index of the element that the caller wishes to
     *            have.
     * @return This method returns the element that corresponds to the given
     *         index.
     */
    public ASExpression get(int index) {
        return _list[index];
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object o) {
        if (!(o instanceof ListExpression))
            return false;
        return Arrays.equals( _list, ((ListExpression) o)._list );
    }
}
