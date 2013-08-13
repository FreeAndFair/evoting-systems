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
 * Wrap a collection of byte arrays. These "arrays" that are collected are each
 * also wrapped. This class exists for the purpose of minimizing byte-by-byte
 * copying of an arrays for the purpose of aggregating several of them over
 * time. If the final array value isn't needed until the very end of some
 * long-running, multi-function process, the intermediate values can simply be
 * stored as a collection of wrapped arrays, rather than copying every byte at
 * each stage of the intermediate format changing.
 * 
 * @author kyle
 * 
 */
public class ByteArrayBuffer {

    private ByteArray[] _arrays;
    private int _position;
    private int _length;

    public static class ByteArray {
        private final byte[] _array;

        public ByteArray(byte[] array) {
            _array = array;
        }
    }

    /**
     * Construct a blank buffer
     */
    public ByteArrayBuffer() {
        _arrays = new ByteArray[100];
        _position = 0;
        _length = 0;
    }

    /**
     * Append an array to this collection.
     * 
     * @param array
     *            Append this array.
     */
    public void append(ByteArray array) {
        if (_position >= _arrays.length)
            grow();
        _length += array._array.length;
        _arrays[_position] = array;
        _position++;
    }

    /**
     * Append a buffer's collection to this collection.
     * 
     * @param buffer
     *            Append each element from the given buffer to this buffer.
     */
    public void append(ByteArrayBuffer buffer) {
        if (_position >= _arrays.length)
            grow();
        for (int lcv = 0; lcv < buffer._position; lcv++)
            append( buffer._arrays[lcv] );
    }

    /**
     * Append a single byte to the list. This will create a single-element array
     * and add this array to the list.
     * 
     * @param b
     *            Add this byte to the list.
     */
    public void append(byte b) {
        byte[] ar = new byte[1];
        ar[0] = b;
        append( new ByteArray( ar ) );
    }

    /**
     * Copy each array in the collection to a buffer of bytes (in order).
     * 
     * @return This method returns a byte array such that the array will consist
     *         of the bytes from each byte-array in the collection, in the order
     *         that they were appended.
     */
    public byte[] getBytes() {
        byte[] ret = new byte[_length];
        int pos = 0;
        for (int lcv = 0; lcv < _position; lcv++) {
            System.arraycopy( _arrays[lcv]._array, 0, ret, pos,
                _arrays[lcv]._array.length );
            pos += _arrays[lcv]._array.length;
        }
        return ret;
    }

    private void grow() {
        ByteArray[] tmp = _arrays;
        _arrays = new ByteArray[tmp.length * 2];
        System.arraycopy( tmp, 0, _arrays, 0, tmp.length );
    }
}
