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

import sexpression.ASExpression;

/**
 * <b>Layers:</b> In an auditorium implementation, each layer is a stage which
 * a message must go through both when it is sent by a host and received by a
 * host. In code, each layer implementation must implement this interface. <br>
 * <br>
 * <b> Method Calls:</b>As should be obvious, each layer should decorate the
 * behavior of each of the methods in this interface of the layer below it. The
 * "links" between layers in an auditorium stack are these method calls. Layers
 * that are higher in the stack (closer to the application) must override
 * methods in this interface such that the behavior for the particular layer is
 * executed either before or after the decorated method call is made. This means
 * that for each method, information either flows from lower layers to higher
 * layers, or from higher layers to lower layers (which dictates whether the
 * decorated method call is made before or after the decorating behavior). This
 * is specified explicitly in the comments for each method. Because each layer
 * has something to contribute both to return values and parameters, return
 * values and parameters are also constructed in a layered manner using
 * s-expressions.<br>
 * <br>
 * When constructing a parameter to pass to a lower layer, do it in the
 * following way:<br>
 * ([action name] [parameter] [previous layer's payload)<br>
 * When constructing a return value, expect your parameter to come in this form
 * as well.<br>
 * <br>
 * 
 * @author kyle
 * 
 */
public interface IAuditoriumLayer {

    /**
     * Make the datum to be sent as part of a join message. Flow: top to bottom.
     * 
     * @param datum
     *            Place this datum in the message.
     * @return The datum to be dropped in the join message.
     */
    public ASExpression makeJoin(ASExpression datum);

    /**
     * Make the datum for a join reply message. Flow: top to bottom.
     * 
     * @param joinmessage
     *            This is the datum from the join message that was received.
     * @return This method returns the join reply datum.
     */
    public ASExpression makeJoinReply(ASExpression joinmessage);

    /**
     * Make the datum for an announcement message. Flow: top to bottom.
     * 
     * @param announcement
     *            Send this announcement.
     * @return This method returns the announcement datum.
     */
    public ASExpression makeAnnouncement(ASExpression announcement);

    /**
     * Process an announcement that was received on the network. Flow: bottom to
     * top.
     * 
     * @param datum
     *            Process this datum.
     * @return This method returns the remaining data after it is unwrapped.
     * 
     * @throws IncorrectFormatException
     *             This method throws if the datum is not formatted how it needs
     *             to be for a given layer to use it correctly.
     */
    public ASExpression receiveAnnouncement(ASExpression datum)
            throws IncorrectFormatException;

    /**
     * Process a join message that was received on the network. Flow: bottom to
     * top.
     * 
     * @param datum
     *            Process this datum.
     * @return After a layer processes the piece of the datum it needs, it
     *         returns the rest.
     * @throws IncorrectFormatException
     *             This method throws if the datum is not formatted how it needs
     *             to be for a given layer to use it correctly.
     */
    public ASExpression receiveJoin(ASExpression datum)
            throws IncorrectFormatException;

    /**
     * Process a join reply that was received on the network. Flow: bottom to
     * top.
     * 
     * @param datum
     *            Process this datum.
     * @return After a layer processes the piece of the datum it needs, it
     *         returns the rest.
     * @throws IncorrectFormatException
     *             This method throws if the datum is not formatted how it needs
     *             to be for a given layer to use it correctly.
     */
    public ASExpression receiveJoinReply(ASExpression datum)
            throws IncorrectFormatException;
}
