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
 * This base class is extended by all auditorium layers.
 * 
 * @author kyle
 * 
 */
public abstract class AAuditoriumLayer implements IAuditoriumLayer {

    /**
     * Use this to serve as the bottom of the stack. (It stops the decoration)
     */
    public static final AAuditoriumLayer BOTTOM = new AAuditoriumLayer( null,
            null ) {

        public ASExpression makeAnnouncement(ASExpression datum) {
            return datum;
        }

        public ASExpression makeJoin(ASExpression datum) {
            return datum;
        }

        public ASExpression makeJoinReply(ASExpression datum) {
            return datum;
        }

        public ASExpression receiveAnnouncement(ASExpression datum)
                throws IncorrectFormatException {
            return datum;
        }

        public ASExpression receiveJoinReply(ASExpression datum)
                throws IncorrectFormatException {
            return datum;
        }

        public ASExpression receiveJoin(ASExpression datum)
                throws IncorrectFormatException {
            return datum;
        }
    };

    private final IAuditoriumLayer _child;
    private final IAuditoriumHost _host;

    /**
     * @param child
     *            This is the child layer.
     * @param host
     *            Adapter to the host of this layer.
     */
    protected AAuditoriumLayer(IAuditoriumLayer child, IAuditoriumHost host) {
        _child = child;
        _host = host;
    }

    /**
     * Get the layer instance which is a child of this layer.
     * 
     * @return This method returns the child layer instance.
     */
    protected IAuditoriumLayer getChild() {
        return _child;
    }

    /**
     * Get the adapter to the host which owns this layer instance. You can use
     * this adapter to get at the message wrapper or to access another layer's
     * public methods.
     * 
     * @return This method returns the adapter to the host that owns this layer.
     */
    protected IAuditoriumHost getHost() {
        return _host;
    }
}
