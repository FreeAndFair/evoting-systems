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

package votebox.crypto;

/**
 * This class represents a 2-tuple (or pair) of BigInteger values. This is
 * useful for representing ElGamal ciphers. These pairs are not mutable.
 * 
 * This was adapted from DSW's original "Tuple" class.
 * 
 * @author kyle
 * 
 */
public class Pair<T> {
    // Actual pair values
    private T _elem1;
    private T _elem2;

    /**
     * Construct a new Pair.
     * 
     * @param elem1
     *            Initialize the tuple with this int in element 1
     * @param elem2
     *            Initialize the tuple with this int in element 2
     */
    public Pair(T elem1, T elem2) {
        _elem1 = elem1;
        _elem2 = elem2;
    }

    /**
     * @return This method returns the first element
     */
    public T get1() {
        return _elem1;
    }

    /**
     * @return This method returns the second element.
     */
    public T get2() {
        return _elem2;
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((_elem1 == null) ? 0 : _elem1.hashCode());
        result = prime * result + ((_elem2 == null) ? 0 : _elem2.hashCode());
        return result;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        final Pair other = (Pair) obj;
        if (_elem1 == null) {
            if (other._elem1 != null)
                return false;
        }
        else if (!_elem1.equals(other._elem1))
            return false;
        if (_elem2 == null) {
            if (other._elem2 != null)
                return false;
        }
        else if (!_elem2.equals(other._elem2))
            return false;
        return true;
    }
    
    @Override
    public String toString(){
    	return "<" + _elem1 + "," + _elem2 + ">";
    }//toString
}
