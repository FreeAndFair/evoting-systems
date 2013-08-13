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

/**
 * An instance of this class represents a list wildcard that constrains slightly
 * more the contents of the list. Each element in the list much match a
 * particular pattern.
 * 
 * @author kyle
 * 
 */
public class ListWildcard extends AWildcard {

    private final ASExpression _pattern;

    public ListWildcard(ASExpression pattern) {
        _pattern = pattern;
    }

    /**
     * @see sexpression.ASExpression#match(sexpression.ASExpression)
     */
    @Override
    public ASExpression match(ASExpression target) {
        if (!(target instanceof ListExpression))
            return NoMatch.SINGLETON;

        ListExpression lst = (ListExpression) target;
        for (ASExpression ase : lst)
            if (_pattern.match( ase ) == NoMatch.SINGLETON)
                return NoMatch.SINGLETON;

        return new ListExpression( target );
    }

    /**
     * @see sexpression.ASExpression#toStringHelp()
     */
    @Override
    public StringBuffer toStringHelp() {
        StringBuffer buffer = new StringBuffer();
        buffer.append( "#list:" );
        buffer.append( _pattern.toStringHelp() );
        buffer.append( "" );
        return buffer;
    }

    /**
     * @see sexpression.ASExpression#size()
     */
    @Override
    public int size() {
        return 0;
    }

    /**
     * @see sexpression.ASExpression#toVerbatimHelp()
     */
    @Override
    public ByteArrayBuffer toVerbatimHelp() {
        ByteArrayBuffer ba = new ByteArrayBuffer();
        ba.append( (byte) '#' );
        ba.append( (byte) 'l' );
        ba.append( _pattern.toVerbatimHelp() );
        return ba;
    }

    /**
     * @see sexpression.ASpecialExpression#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object o) {
        if (!(o instanceof ListWildcard))
            return false;

        return ((ListWildcard) o)._pattern.equals( _pattern );
    }
}
