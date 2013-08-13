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

import sexpression.ByteArrayBuffer.ByteArray;
import sexpression.stream.Base64;
import java.lang.ref.WeakReference;
import java.util.Arrays;
import java.util.HashMap;

/**
 * A ByteStringExpression is an SExpression. In particular, a
 * ByteStringExpression is, simply, an ordering of ASCII characters.
 * 
 * @author Kyle
 */
public class StringExpression extends ASExpression {

    public static class BytesBox {
        private final byte[] _bytes;

        private BytesBox(byte[] bytes) {
            _bytes = bytes;
        }

        @Override
        public boolean equals(Object o) {
            if (!(o instanceof BytesBox))
                return false;

            return Arrays.equals(_bytes, ((BytesBox) o)._bytes);
        }

        @Override
        public int hashCode() {
            return (((int) _bytes[0]) << 24) | (((int) _bytes[1]) << 16)
                    | (((int) _bytes[2]) << 8) | (int) _bytes[3];
        }
    }

    public static final StringExpression EMPTY = new StringExpression();
    public static final HashMap<BytesBox, WeakReference<StringExpression>> _interned = new HashMap<BytesBox, WeakReference<StringExpression>>();

    /**
     * Ask for an expression that represents the given string. This method
     * checks if one has already been interned, and if it has, returns it, other
     * wise constructs a new one and adds it to the intern map.
     * 
     * @param string
     *            Make an expression that represents this string.
     * @return This method returns the interned expression that represents the
     *         given string.
     */
    public static StringExpression makeString(String string) {
        if (string.equals(""))
            return EMPTY;
        return makeString(string.getBytes());
    }

    /**
     * Ask for an expression that represents the given byte array. This method
     * checks if one has already been interned, and if it has, returns it,
     * otherwise constructs a new one and adds it to the intern map.
     * 
     * @param bytes
     *            Make an expression that represents this set of bytes as a string.
     * @return This method returns the interned expression that represents the
     *         given byte string.
     */
    public static StringExpression makeString(byte[] bytes) {
        BytesBox hash = new BytesBox(ASExpression.computeSHA1(bytes));
        synchronized (_interned) {
            if (_interned.containsKey(hash)
                    && _interned.get(hash).get() != null)
                return _interned.get(hash).get();

            StringExpression retval = new StringExpression(bytes);
            _interned.put(new BytesBox(ASExpression.computeSHA1(bytes)),
                    new WeakReference<StringExpression>(retval));
            return retval;
        }

    }

    private byte[] _bytes;

    /**
     * Construct a string sexp that is empty.
     */
    private StringExpression() {
        _bytes = new byte[0];
    }

    /**
     * This is a constructor for ByteStringExpression
     * 
     * @param bytes
     */
    private StringExpression(byte[] bytes) {
        _bytes = bytes;
    }

    /**
     * For byte strings, return the string that represents the byte string. Use
     * java.lang.String's constructor.
     * 
     * 
     * @see sexpression.ASExpression#toString()
     */
    public StringBuffer toStringHelp() {
        StringBuffer buffer = new StringBuffer();
        for (byte b : _bytes)
            if ((b > 32 && b < 127) || Character.isWhitespace((char) b))
                buffer.append((char) b);
            else
                return toPrettifiedString();
        return buffer;
    }

    /**
     * This is a helper method for toString. Surround the byte values in '[]'.
     * Call this method if the byte values don't really work as characters.
     * 
     * @return This method returns the string with byte values surrounded in
     *         brackets.
     */
    private StringBuffer toPrettifiedString() {
        StringBuffer buffer = new StringBuffer();
        buffer.append("{");
        buffer.append(Base64.encodeBytes(_bytes));
        buffer.append("}");
        return buffer;
    }

    /**
     * A string, x, is represented in verbatim by the string "len(x):x"
     * 
     * 
     * @see sexpression.ASExpression#toVerbatim()
     */
    public ByteArrayBuffer toVerbatimHelp() {
        ByteArrayBuffer buf = new ByteArrayBuffer();
        ByteArray length = new ByteArray(Integer.toString(_bytes.length)
                .getBytes());
        buf.append(length);
        buf.append((byte) ':');
        buf.append(new ByteArray(_bytes));
        return buf;
    }

    /**
     * @see sexpression.ASExpression#match(sexpression.ASExpression)
     */
    @Override
    public synchronized ASExpression match(ASExpression target) {
        if (this == target)
            return ListExpression.EMPTY;
        return NoMatch.SINGLETON;
    }

    /**
     * @see sexpression.ASExpression#namedMatch(sexpression.ASExpression)
     */
    @Override
    public synchronized HashMap<String, ASExpression> namedMatch(
            ASExpression target) {
        if (this == target)
            return new HashMap<String, ASExpression>();
        return NamedNoMatch.SINGLETON;
    }

    /**
     * This method returns a copy of the bytes. Because s-expressions are
     * immutable, we do not wish to return the actual data.
     * 
     * @return This method returns a copy of the byte string.
     */
    public byte[] getBytesCopy() {
        byte[] returnarray = new byte[_bytes.length];
        System.arraycopy(_bytes, 0, returnarray, 0, _bytes.length);
        return returnarray;
    }

    /**
     * Do not use this unless you know what you're doing!
     * 
     * @return This returns a ref to the actual byte array that backs the string
     *         expression. DO NOT MUTATE THIS.
     */
    public byte[] getBytes() {
        return _bytes;
    }

    /**
     * Call this method to get a given byte from the string.
     * 
     * @param index
     *            This is the index of the wanted byte.
     * @return This method returns the indexth byte from the string.
     */
    public byte get(int index) {
        return _bytes[index];
    }

    /**
     * Return the number of bytes in this string.
     * 
     * @return This method returns the number of bytes in this string.
     */
    public int size() {
        return _bytes.length;
    }

    /**
     * @see java.lang.Object#finalize()
     */

    @Override
    public void finalize() {
        _interned.remove(new BytesBox(_bytes));
    }
    
    /**
     * 
     */
    @Override
    public boolean equals(Object o){
    	if(!(o instanceof StringExpression))
    		return false;
    	
    	return toString().equals(o.toString());
    }
}
