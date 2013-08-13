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

package auditorium;

import sexpression.*;

/**
 * This class represents the ptr auditorium data structure. Its format is (ptr
 * [nodeid] [sequence num] [hash]).
 * 
 * @author kyle
 * 
 */
public class MessagePointer {

    public static final ASExpression PATTERN = new ListExpression(
            StringExpression.makeString( "ptr" ), StringWildcard.SINGLETON,
            StringWildcard.SINGLETON, StringWildcard.SINGLETON );
    public static final MessagePointer NULL = new MessagePointer( "", "",
            StringExpression.EMPTY );

    private final String _nodeid;
    private final String _number;
    private final StringExpression _hash;

    // lazy eval
    private ASExpression _aseform;

    /**
     * @param machine
     *            Point to this machine.
     * @param number
     *            Point to this message number from machine.
     * @param hash
     *            This is the hash of the message this points to.
     */
    public MessagePointer(String machine, String number, StringExpression hash) {
        _nodeid = machine;
        _number = number;
        _hash = hash;
    }

    /**
     * Convert a message pointer from its sexp form to it's object form.
     * 
     * @param exp
     *            Convert this sexp.
     * @return This method returns the given message pointer in sexp form after
     *         it has been converted to object form.
     * @throws IncorrectFormatException
     *             This method throws if the given expression is not (ptr
     *             [nodeid] [sequence num] [hash]).
     */
    public MessagePointer(ASExpression exp) throws IncorrectFormatException {
        ASExpression result = PATTERN.match( exp );
        if (result == NoMatch.SINGLETON)
            throw new IncorrectFormatException( exp, new Exception( exp
                    + " doesn't match the pattern: " + PATTERN ) );
        _nodeid = ((ListExpression) result).get( 0 ).toString();
        _number = ((ListExpression) result).get( 1 ).toString();
        _hash = (StringExpression) ((ListExpression) result).get( 2 );
    }

    /**
     * Construct a pointer to a given message.
     * 
     * @param message
     *            Construct a pointer to this message.
     */
    public MessagePointer(Message message) {
        _nodeid = message.getFrom().getNodeId();
        _hash = message.getHash();
        _number = message.getSequence();
    }

    /**
     * Get the machine ID of the message this points to.
     * 
     * @return This method returns the machine ID of the message this points to.
     */
    public String getNodeId() {
        return _nodeid;
    }

    /**
     * Get the message number of the message that this points to.
     * 
     * @return This method returns the message number of the message that this
     *         points to.
     */
    public String getNumber() {
        return _number;
    }

    /**
     * Get the hash of the message that this points to.
     * 
     * @return This method returns the hash of the message that this points to.
     */
    public StringExpression getHash() {
        return _hash;
    }

    /**
     * Convert this message pointer to its sexp form.
     * 
     * @return This method returns this message pointer in its sexp form.
     */
    public ASExpression toASE() {
        if (_aseform == null)
            _aseform = new ListExpression(
                    StringExpression.makeString( "ptr" ), StringExpression
                            .makeString( _nodeid ), StringExpression
                            .makeString( _number ), _hash );

        return _aseform;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object o) {
        if (!(o instanceof MessagePointer))
            return false;

        MessagePointer other = (MessagePointer) o;
        return this._number.equals( other._number )
                && this._nodeid.equals( other._nodeid )
                && this._hash.equals( other._hash );
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return _hash.hashCode();
    }

    /**
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return "{machine:" + _nodeid + " message:" + _number + "}";
    }
}
