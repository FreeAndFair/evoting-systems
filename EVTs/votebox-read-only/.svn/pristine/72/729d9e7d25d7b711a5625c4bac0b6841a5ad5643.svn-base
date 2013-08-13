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
 * An instance of this class simply wraps an ID, IP and port together. This
 * class represents a data structure in the auditorium format.
 * 
 * @author kyle
 * 
 */
public class HostPointer {

    public static final ASExpression PATTERN = new ListExpression(
            StringExpression.makeString( "host" ), StringWildcard.SINGLETON,
            StringWildcard.SINGLETON, StringWildcard.SINGLETON );

    private final String _nodeid;
    private final String _ip;
    private final int _port;

    // lazy eval save
    private ListExpression _aseform;
    private String _string;

    /**
     * @param nodeid
     *            This is the id of the host.
     * @param ip
     *            This is the IP of the host in dotted decimal format.
     * @param port
     *            This is the port that the host is listening on.
     */
    public HostPointer(String nodeid, String ip, int port) {
        _nodeid = nodeid;
        _port = port;
        _ip = ip;
    }

    /**
     * Construct a new host address from its s-expression representation.
     * 
     * @param hostexp
     *            This should be of the format (host [id] [ip] [port])
     * @throws IncorrectFormatException
     *             This method throws if the given exp is not correctly
     *             formatted.
     */
    public HostPointer(ASExpression hostexp) throws IncorrectFormatException {
        try {
            ASExpression result = PATTERN.match( hostexp );
            if (result == NoMatch.SINGLETON)
                throw new IncorrectFormatException( hostexp, new Exception(
                        hostexp + " didn't match the pattern " + PATTERN ) );
            _nodeid = ((ListExpression) result).get( 0 ).toString();
            _ip = ((ListExpression) result).get( 1 ).toString();
            _port = Integer.parseInt( ((ListExpression) result).get( 2 )
                    .toString() );
        }
        catch (NumberFormatException e) {
            throw new IncorrectFormatException( hostexp, e );
        }
    }

    /**
     * Get the id of the node this references.
     * 
     * @return This method returns the node id.
     */
    public String getNodeId() {
        return _nodeid;
    }

    /**
     * Get the IP of this host.
     * 
     * @return This method returns the IP of this host.
     */
    public String getIP() {
        return _ip;
    }

    /**
     * Get the port of this host.
     * 
     * @return This method returns the port of this host.
     */
    public int getPort() {
        return _port;
    }

    /**
     * Return the sexpression representation of this host pointer.
     * 
     * @return This method returns (host _nodeid _ip _port)
     */
    public ListExpression toASE() {
        if (_aseform == null)
            _aseform = new ListExpression(
                    StringExpression.makeString( "host" ), StringExpression
                            .makeString( _nodeid ), StringExpression
                            .makeString( _ip ), StringExpression
                            .makeString( Integer.toString( _port ) ) );

        return _aseform;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object o) {
        if (!(o instanceof HostPointer))
            return false;
        HostPointer hpo = (HostPointer) o;

        return _nodeid.equals( hpo._nodeid ) && _ip.equals( hpo._ip )
                && _port == hpo._port;
    }

    /**
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        if (_string == null)
            _string = _nodeid + "@" + _ip + ":" + Integer.toString( _port );

        return _string;
    }

}
