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

package sexpression.stream;

import java.io.EOFException;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;

import sexpression.*;

/**
 * The ASEInputStreamReader parses ASExpressions that have been serialized in
 * verbatim form off any input stream.
 * 
 * @author Kyle
 * 
 */
public class ASEInputStreamReader {

    public static final byte ANY = 'a';
    public static final byte STRING = 's';
    public static final byte WILDCARD = 'w';
    public static final byte LIST = 'l';
    public static final byte NOTHING = 'n';
    public static final byte NOMATCH = 'f';

    private InputStream _stream;
    private InputStream _base64Stream;
    private InputStream _standardStream;

    /**
     * @param stream
     *            This is the stream off which ASExpressions are parsed.
     */
    public ASEInputStreamReader(InputStream stream) {
        _standardStream = stream;
        _base64Stream = new Base64.InputStream( stream );
    }

    /**
     * Invoke this method to parse one ASExpression off the decorated stream.
     * This method interprets the stream to have ASExpressions in either
     * verbatim or base64/canonical form delineated by nothing. (In other words,
     * s-expressions in the verbatim form should be "back to back" on the stream
     * in order for subsequent calls to read() to give the desired behavior..)
     * 
     * @return This method returns the parsed ASExpression.
     * @throws IOException
     *             This method throws if reading from the decorated stream
     *             throws.
     * @throws InvalidVerbatimStreamException
     *             This method throws if there is invalid data on the stream. In
     *             order for s-expressions to be valid, the must begin either
     *             with a digit (denoting a string type) or a paren (denoting a
     *             list). If the parser expects one of these two and finds
     *             something else, the data is invalid.
     */
    public ASExpression read() throws IOException,
            InvalidVerbatimStreamException {
        // Read in the first byte to check for type: base64 or standard
        // verbatim.
        _stream = _standardStream;
        byte b = (byte) _stream.read();
        // base64/canonical case
        if (b == '{') {
            _stream = _base64Stream;
            ASExpression returnv = readASE( (byte) _stream.read() );

            return returnv;
        }
        // EOF case.
        else if (b == -1)
            throw new EOFException( "End of stream" );
        // verbatim case
        else
            return readASE( (byte) b );
    }

    /**
     * This is a private helper method for read(). This method will call either
     * readString(...) or readList() for help, based on if the first character
     * of the next s-expression on the stream is a digit or an open paren.
     * Important: this method expects that this first (and crucial) character
     * has already been read off the stream.
     * 
     * @param openchar
     *            This is the (crucial) character which this method uses to
     *            determine if the next s-expression is type list or string.
     * @return This method returns the next s-expression on the list as an
     *         ASExpression.
     * @throws IOException
     *             This method throws if reading from the decorated stream
     *             throws.
     * @throws InvalidVerbatimStreamException
     *             This method throws if there is invalid data on the stream. In
     *             order for s-expressions to be valid, the must begin either
     *             with a digit (denoting a string type) or a paren (denoting a
     *             list). If the parser expects one of these two and finds
     *             something else, the data is invalid.
     */
    private ASExpression readASE(byte openchar) throws IOException,
            InvalidVerbatimStreamException {

        switch (openchar) {
        case '(':
            return readList();
        case '#':
            return readWildcard();
        case '%':
            return readNamedPattern();
        case -1:
            throw new EOFException( "End of stream" );
        }

        if (Character.isDigit( openchar )) {
            return readString( openchar );
        }

        throw new InvalidVerbatimStreamException( "read: '" + (char)openchar
                + "' as "+openchar+": expected to be a number, '(', '#', or '%'." );
    }

    /**
     * This is a private helper method for readASE(). This method parses the
     * remainder of a named pattenr expression, assuming the first character
     * (the '%') has already been read.
     * 
     * @return This method returns the ASExpression that represents the named
     *         pattern sitting on the verbatim stream.
     */
    private ASExpression readNamedPattern() throws IOException,
            InvalidVerbatimStreamException {
        ASExpression s = readString( (byte) _stream.read() );
        ASExpression p = read();
        return new NamedPattern( s.toString(), p );
    }

    /**
     * This is a private helper method for readASE(). This method parses the
     * remainder of a wildcard expression, assuming the first character (the
     * '#') has already been read.
     * 
     * @return This method returns the ASExpression that represents the wildcard
     *         sitting on the verbatim stream.
     */
    private ASExpression readWildcard() throws IOException,
            InvalidVerbatimStreamException {
        byte b = (byte) _stream.read();

        switch (b) {
        case ANY:
            return Wildcard.SINGLETON;
        case STRING:
            return StringWildcard.SINGLETON;
        case WILDCARD:
            return WildcardWildcard.SINGLETON;
        case NOTHING:
            return Nothing.SINGLETON;
        case NOMATCH:
            return NoMatch.SINGLETON;
        case LIST:
            return new ListWildcard( read() );
        }
        throw new InvalidVerbatimStreamException(
                "# wasn't followed by an acceptable byte" );
    }

    /**
     * This is a private helper method for readASE(). This method reads one byte
     * string off the stream and constructs a new StringExpression which
     * represents it. Important: This method assumes that the length and the
     * colon have already been read off the stream!
     * 
     * @param len
     *            This method will read this number of bytes off the stream to
     *            construct the StringExpression
     * @return This method returns the constructed StringExpression which
     *         represents the string read off the stream.
     * @throws IOException
     *             This method throws if there was a problem reading the proper
     *             number of bytes off the stream (basically, EOF).
     */
    private ASExpression readString(byte openchar) throws IOException {
        int b;
        StringBuffer buffer = new StringBuffer();
        buffer.append( (char) openchar );
        // Read until the colon to get len
        while ((b = _stream.read()) != ':')
            buffer.append( (char) b );

        // Read the string and return it
        int len = Integer.parseInt( buffer.toString() );

        // Read len bytes
        byte[] ba = new byte[len];
        int off = 0;

        // Keep reading from the stream until we get enough bytes or die trying.
        while (off != len) {
            off += _stream.read( ba, off, (len - off) );
        }

        // Convert to unicode string, create an ASExpression that represents
        // this node.
        return StringExpression.makeString( ba );
    }

    /**
     * This is a private helper method for readASE(). This method parses a list
     * s-expression off the stream and constructs a new SExpressionlist which
     * represents it. Important: This method assumes that the open paren for the
     * list has already been read off the stream!
     * 
     * @return This method returns the new SExpressionList which represents what
     *         was parsed off the stream.
     * @throws IOException
     *             This method throws if there was a problem reading the proper
     *             number of bytes off the stream.
     * @throws InvalidVerbatimStreamException
     *             This method
     */
    private ListExpression readList() throws IOException,
            InvalidVerbatimStreamException {
        ArrayList<ASExpression> list = new ArrayList<ASExpression>();
        int b;

        // parse ASExpressions off the stream until you read in ')' which
        // denotes the end of the list
        while ((b = _stream.read()) != ')')
            list.add( readASE( (byte) b ) );

        return new ListExpression( list );
    }
}
