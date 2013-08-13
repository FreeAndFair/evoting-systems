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
 * An instance of this class represents an auditorium wire message. Messages on
 * the wire are of the form ([name] [host] [sequence] [datum]).
 * 
 * @author kyle
 * 
 */
public class Message {

    public static final ASExpression PATTERN = new ListExpression(
            StringWildcard.SINGLETON, HostPointer.PATTERN,
            StringWildcard.SINGLETON, Wildcard.SINGLETON );

    private final String _type;
    private final HostPointer _from;
    private final String _sequence;
    private final ASExpression _datum;

    // lazy eval save fields
    private ASExpression _aseform = null;
    private StringExpression _hash = null;

    /**
     * @param type
     *            Construct a message of this type. This should be one of
     *            "join", "join-reply", "discover", "discover-reply", and
     *            "announce".
     * @param from
     *            Construct a message as being from this host.
     * @param sequence
     *            Construct of a message that has this sequence number.
     * @param datum
     *            Construct a message that has this datum.
     */
    public Message(String type, HostPointer from, String sequence,
            ASExpression datum) {
        _type = type;
        _from = from;
        _sequence = sequence;
        _datum = datum;
    }

    /**
     * Construct a message from its s-expression format.
     * 
     * @param message
     *            Construct a message from this s-expression
     * @throws IncorrectFormatException
     *             This method throws if the s-expression given is not in the
     *             correct format: ([name] [host] [sequence] [datum]).
     */
    public Message(ASExpression message) throws IncorrectFormatException {
        if (PATTERN.match( message ) == NoMatch.SINGLETON)
            throw new IncorrectFormatException( message, new Exception( message
                    + " didn't match the pattern:" + PATTERN ) );
        ListExpression lst = (ListExpression) message;
        _type = ((StringExpression) lst.get( 0 )).toString();
        _from = new HostPointer( lst.get( 1 ) );
        _sequence = lst.get( 2 ).toString();
        _datum = lst.get( 3 );
    }

    /**
     * Convert this message into a form that can be placed on the wire.
     * 
     * @return This method returns ([name] [host] [datum]).
     */
    public ASExpression toASE() {
        if (_aseform == null)
            _aseform = new ListExpression(
                    StringExpression.makeString( _type ), _from.toASE(),
                    StringExpression.makeString( _sequence ), _datum );
        return _aseform;
    }

    /**
     * Get the hash of this message.
     * 
     * @return This method returns the hash of this message.
     */
    public StringExpression getHash() {
        if (_hash == null)
            _hash = StringExpression.makeString( toASE().getSHA1() );
        return _hash;
    }

    /**
     * Get the type field for this message.
     * 
     * @return This method returns the type field for this message.
     */
    public String getType() {
        return _type;
    }

    /**
     * Get the from field for this message.
     * 
     * @return This method returns the from field for this message.
     */
    public HostPointer getFrom() {
        return _from;
    }

    /**
     * Get the sequence number of this message.
     * 
     * @return This method returns the sequence number of this message.
     */
    public String getSequence() {
        return _sequence;
    }

    /**
     * Get the datum field for this message.
     * 
     * @return This method returns the datum field for this message.
     */
    public ASExpression getDatum() {
        return _datum;
    }

    /**
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return toASE().toString();
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object o) {
        if (!(o instanceof Message))
            return false;
        try {
            return new MessagePointer( toASE() ).equals( new MessagePointer(
                    ((Message) o).toASE() ) );
        }
        catch (IncorrectFormatException e) {
            return false;
        }
    }
}
