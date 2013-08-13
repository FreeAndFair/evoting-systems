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

package auditorium.test;

import static org.junit.Assert.*;

import java.math.BigInteger;

import org.junit.*;
import sexpression.*;
import auditorium.*;

/**
 * This class offers JUnit testing of the auditorium.Cert class.
 * 
 * @author kyle
 * 
 */
public class CertTest {

    private final Key _key = new Key( "KEYID", "KEYANNOTATION", new BigInteger(
            "1" ), new BigInteger( "2" ) );
    private final ASExpression _keyase = _key.toASE();

    private final Signature _sig = new Signature( "signer",
            StringExpression.makeString( "sigdata" ), _key.toASE() );

    // ** <init>(String, StringExpression, Key) tests **
    // the payload of the signature isn't a key.
    @Test(expected = IncorrectFormatException.class)
    public void constructor1_1() throws Exception {
        new Cert( new Signature( "signer", StringExpression.makeString( "sigdata" ),
                ListExpression.EMPTY ) );
    }

    // Good
    @Test
    public void constructor1_2() throws Exception {
        Cert c = new Cert( _sig );

        assertEquals( _sig.toASE(), c.getSignature().toASE() );
        assertEquals( _key.toASE(), c.getKey().toASE() );
        assertEquals( new ListExpression( StringExpression.makeString( "cert" ),
                new ListExpression( StringExpression.makeString( "signature" ),
                        StringExpression.makeString( "signer" ), StringExpression.makeString(
                                "sigdata" ), _keyase ) ), c.toASE() );

    }

    // ** <init>(ASExpression) tests **
    // Junk
    @Test(expected = IncorrectFormatException.class)
    public void constructor2_1() throws IncorrectFormatException {
        new Cert( StringExpression.EMPTY );
    }

    @Test(expected = IncorrectFormatException.class)
    public void constructor2_2() throws IncorrectFormatException {
        new Cert( new ListExpression( "non", "sense" ) );
    }

    // len < 2
    @Test(expected = IncorrectFormatException.class)
    public void constructor2_3() throws IncorrectFormatException {
        new Cert( new ListExpression( "cert" ) );
    }

    // len > 2
    @Test(expected = IncorrectFormatException.class)
    public void constructor2_4() throws IncorrectFormatException {
        new Cert( new ListExpression( StringExpression.makeString( "cert" ),
                new ListExpression( StringExpression.makeString( "signature" ),
                        StringExpression.makeString( "signer" ), StringExpression.makeString(
                                "Sig" ), _keyase ), StringExpression.makeString(
                        "extra" ) ) );
    }

    // [0] != cert
    @Test(expected = IncorrectFormatException.class)
    public void constructor2_5() throws IncorrectFormatException {
        new Cert( new ListExpression( StringExpression.makeString( "notcert" ),
                new ListExpression( StringExpression.makeString( "signature" ),
                        StringExpression.makeString( "signer" ), StringExpression.makeString(
                                "Sig" ), _keyase ) ) );
    }

    // [1] !signature
    @Test(expected = IncorrectFormatException.class)
    public void constructor2_6() throws IncorrectFormatException {
        new Cert( new ListExpression( StringExpression.makeString( "cert" ),
                new ListExpression( StringExpression.makeString( "notsignature" ),
                        StringExpression.makeString( "signer" ), StringExpression.makeString(
                                "Sig" ), _keyase ) ) );
    }

    // Good
    @Test
    public void constructor2_7() throws IncorrectFormatException {
        Cert c = new Cert( new ListExpression( StringExpression.makeString( "cert" ),
                new ListExpression( StringExpression.makeString( "signature" ),
                        StringExpression.makeString( "signer" ), StringExpression.makeString(
                                "Sig" ), _keyase ) ) );

        assertEquals( new Signature( "signer", StringExpression.makeString( "Sig" ),
                _keyase ).toASE(), c.getSignature().toASE() );
        assertEquals( _keyase, c.getKey().toASE() );
        assertEquals( new ListExpression( StringExpression.makeString( "cert" ),
                new ListExpression( StringExpression.makeString( "signature" ),
                        StringExpression.makeString( "signer" ), StringExpression.makeString(
                                "Sig" ), _keyase ) ), c.toASE() );

    }
}
