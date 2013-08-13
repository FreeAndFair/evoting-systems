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

import java.util.ArrayList;

import sexpression.*;

/**
 * This layer deals with temporality assertions in announcements. That is, it
 * asserts which message or messages was or were previous to each message placed
 * on the wire. This is where the entanglement happens.<br>
 * <br>
 * 
 * @author kyle
 * 
 */
public class AuditoriumTemporalLayer extends AAuditoriumLayer {

    public static final ASExpression PATTERN = new ListExpression(
            StringExpression.makeString( "succeeds" ), new ListWildcard(
                    MessagePointer.PATTERN ), Wildcard.SINGLETON );
    public static final ASExpression REPLY_PATTERN = new ListWildcard(
            MessagePointer.PATTERN );

    /**
     * @param child
     *            This layer is below the constructed layer.
     * @param host
     *            This is the host that is using this new layer.
     */
    public AuditoriumTemporalLayer(AAuditoriumLayer child, IAuditoriumHost host) {
        super( child, host );
    }

    /**
     * @see auditorium.IAuditoriumLayer#makeAnnouncement(sexpression.ASExpression)
     */
    public ASExpression makeAnnouncement(ASExpression datum) {
        // Make new datum - Wrap with everything that is in the last list.
        ArrayList<ASExpression> list = new ArrayList<ASExpression>();
        for (MessagePointer p : getHost().getLog().getLast())
            list.add( p.toASE() );
        ASExpression newdatum = new ListExpression( StringExpression
                .makeString( "succeeds" ), new ListExpression( list ), datum );

        // Make decorated method call
        return getChild().makeAnnouncement( newdatum );
    }

    /**
     * @see auditorium.IAuditoriumLayer#makeJoin(sexpression.ASExpression)
     */
    public ASExpression makeJoin(ASExpression datum) {
        return getChild().makeJoin( datum );
    }

    /**
     * @see auditorium.IAuditoriumLayer#makeJoinReply(sexpression.ASExpression)
     */
    public ASExpression makeJoinReply(ASExpression datum) {
        // Make new datum - Construct the last list to return to the requesting
        // host.
        ArrayList<ASExpression> lst = new ArrayList<ASExpression>();
        for (MessagePointer mp : getHost().getLog().getLast())
            lst.add( mp.toASE() );
        ASExpression newdatum = new ListExpression( lst );

        // Make decorated method call.
        return getChild().makeJoinReply( newdatum );
    }

    /**
     * @see auditorium.IAuditoriumLayer#receiveAnnouncement(sexpression.ASExpression)
     */
    public ASExpression receiveAnnouncement(ASExpression datum)
            throws IncorrectFormatException {
        // Make decorated method call
        ASExpression result = PATTERN.match( getChild().receiveAnnouncement(
            datum ) );
        if (result == NoMatch.SINGLETON)
            throw new IncorrectFormatException( datum, new Exception( datum
                    + " doesn't match the pattern: " + PATTERN ) );

        // Extract message pointers that are now "seen"
        for (ASExpression ase : (ListExpression) ((ListExpression) result)
                .get( 0 )) {
            getHost().getLog().removeFromLast( new MessagePointer( ase ) );
        }

        // push the rest of the data up the stack..
        return ((ListExpression) result).get( 1 );
    }

    /**
     * @see auditorium.IAuditoriumLayer#receiveJoinReply(sexpression.ASExpression)
     */
    public ASExpression receiveJoinReply(ASExpression datum)
            throws IncorrectFormatException {
        // Make decorated method call.
        ASExpression result = REPLY_PATTERN.match( getChild().receiveJoinReply(
            datum ) );
        if (result == NoMatch.SINGLETON)
            throw new IncorrectFormatException( datum, new Exception( datum
                    + " didn't match the pattern " + REPLY_PATTERN ) );

        ListExpression below = (ListExpression) ((ListExpression) result)
                .get( 0 );
        // Extract message pointers to be added to the last list.
        for (ASExpression ase : ((ListExpression) below))
            getHost().getLog().updateLast( new MessagePointer( ase ) );

        // There is no more data to return.
        return Nothing.SINGLETON;

    }

    /**
     * @see auditorium.IAuditoriumLayer#receiveJoin(sexpression.ASExpression)
     */
    public ASExpression receiveJoin(ASExpression datum)
            throws IncorrectFormatException {
        return getChild().receiveJoin( datum );
    }
}
