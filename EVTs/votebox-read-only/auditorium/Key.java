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

import java.math.BigInteger;

import sexpression.*;

/**
 * This class represents one half of an asymmetric cryptographic key; as such it
 * can be used for signing, as well as <i>either</i> encryption or decryption.
 * It is an RSA key defined by a modulus and a single exponent (both using
 * BigInteger math). Also included is an identifier (helpful for
 * associating the key with, for example, an external entity) and a free-form
 * annotation.
 * <p>
 * Its S-expression representation (used for wire-protocol transmission as well
 * as storage, e.g. in a {@link auditorium.SimpleKeyStore}) is:
 * <p>
 * <tt>
 * (key <i>id</i> <i>annotation</i> <i>mod</i> <i>exp</i>)
 * </tt>
 * 
 * @see sexpression
 * @author kyle
 * 
 */
public class Key {

    public static final ASExpression PATTERN = new ListExpression(
            StringExpression.makeString( "key" ), StringWildcard.SINGLETON,
            StringWildcard.SINGLETON, StringWildcard.SINGLETON,
            StringWildcard.SINGLETON );

    private final String _id;
    private final String _annotation;
    private final BigInteger _mod;
    private final BigInteger _key;

    /**
     * @param id
     *            The key belongs to the host that has this ID
     * @param annotation
     *            The key is annotated with this string (usually something about
     *            how the key is supposed to be used)
     * @param mod
     *            This is the key's modulus, the product of two large primes.
     * @param key
     *            This is the actual key material (in RSA, it is an exponent).
     */
    public Key(String id, String annotation, BigInteger mod, BigInteger key) {
        _id = id;
        _annotation = annotation;
        _mod = mod;
        _key = key;
    }

    /**
     * @param expression
     *            Construct the key from this expression. This should be the get
     *            in s-expression format (like what is returned from toASE())
     * @throws IncorrectFormatException
     *             This method throws if the given expression is not formatted
     *             correctly.
     */
    public Key(ASExpression expression) throws IncorrectFormatException {
        try {
            ASExpression matchresult = PATTERN.match( expression );
            if (matchresult == NoMatch.SINGLETON)
                throw new IncorrectFormatException( expression, new Exception(
                        "did not match the pattern for key" ) );
            ListExpression matchlist = (ListExpression) matchresult;

            _id = matchlist.get( 0 ).toString();
            _annotation = matchlist.get( 1 ).toString();
            _mod = new BigInteger( ((StringExpression) matchlist.get( 2 ))
                    .getBytesCopy() );
            _key = new BigInteger( ((StringExpression) matchlist.get( 3 ))
                    .getBytesCopy() );
        }
        catch (ClassCastException e) {
            throw new IncorrectFormatException( expression, e );
        }
    }

    /**
     * Construct an s-expression which represents this key.
     * 
     * @return This method returns (key [id] [annotation] [mod] [exp]).
     */
    public ASExpression toASE() {
        return new ListExpression( StringExpression.makeString( "key" ),
                StringExpression.makeString( _id ), StringExpression
                        .makeString( _annotation ), StringExpression
                        .makeString( _mod.toByteArray() ), StringExpression
                        .makeString( _key.toByteArray() ) );
    }

    /**
     * @return This method returns the ID of the host that this key belongs to.
     */
    public String getId() {
        return _id;
    }

    /**
     * @return This method returns the annotation string given to this key.
     */
    public String getAnnotation() {
        return _annotation;
    }

    /**
     * @return This method returns the key's modulus number.
     */
    public BigInteger getMod() {
        return _mod;
    }

    /**
     * @return This method returns the key's exponent.
     */
    public BigInteger getKey() {
        return _key;
    }
}
