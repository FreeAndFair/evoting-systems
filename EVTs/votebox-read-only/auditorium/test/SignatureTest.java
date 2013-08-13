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

import auditorium.*;
import org.junit.*;
import sexpression.*;
import static org.junit.Assert.*;

public class SignatureTest {

    // ** <init>(String, StringExpression, ASExpression) tests **
    @Test
    public void constructor1_1() {
        Signature sig = new Signature( "ID", StringExpression.makeString( "sigdata" ),
                StringExpression.EMPTY );

        assertEquals( "ID", sig.getId() );
        assertEquals( "sigdata", sig.getSigData().toString() );
        assertEquals( StringExpression.EMPTY, sig.getPayload() );
        assertEquals( new ListExpression( "signature", "ID", "sigdata", "" ),
            sig.toASE() );
    }

    @Test
    public void constructor1_2() {
        Signature sig = new Signature( "awesomeID", StringExpression.makeString(
                "datadata" ), StringExpression.makeString( "payload" ) );

        assertEquals( "awesomeID", sig.getId() );
        assertEquals( "datadata", sig.getSigData().toString() );
        assertEquals( StringExpression.makeString( "payload" ), sig.getPayload() );
        assertEquals( new ListExpression( "signature", "awesomeID", "datadata",
                "payload" ), sig.toASE() );
    }

    // **<init>(ASExpression) tests **
    // Junk
    @Test(expected = IncorrectFormatException.class)
    public void constructor2_1() throws Exception {
        new Signature( NoMatch.SINGLETON );
    }

    @Test(expected = IncorrectFormatException.class)
    public void constructor2_2() throws Exception {
        new Signature( StringExpression.EMPTY );
    }

    // len < 4
    @Test(expected = IncorrectFormatException.class)
    public void constructor2_3() throws Exception {
        new Signature( new ListExpression( "signature", "id", "sigdata" ) );
    }

    // len > 4
    @Test(expected = IncorrectFormatException.class)
    public void constructor2_4() throws Exception {
        new Signature( new ListExpression( "signature", "id", "sigdata",
                "payload", "extra" ) );
    }

    // [0] != "signature"
    @Test(expected = IncorrectFormatException.class)
    public void constructor2_5() throws Exception {
        new Signature( new ListExpression( "notsignature", "id", "sigdata",
                "payload" ) );
    }

    // [1] not a string
    @Test(expected = IncorrectFormatException.class)
    public void constructor2_6() throws Exception {
        new Signature( new ListExpression( StringExpression.makeString( "signature" ),
                new ListExpression( "id" ), StringExpression.makeString( "sigdata" ),
                StringExpression.makeString( "payload" ) ) );
    }

    // [2] not a string
    @Test(expected = IncorrectFormatException.class)
    public void constructor2_7() throws Exception {
        new Signature( new ListExpression( StringExpression.makeString( "signature" ),
                StringExpression.makeString( "id" ), new ListExpression( "sigdata" ),
                StringExpression.makeString( "payload" ) ) );
    }

    // Good
    @Test
    public void constructor2_8() throws Exception {
        Signature sig = new Signature( new ListExpression( "signature",
                "awesomeID", "datadata", "payload" ) );

        assertEquals( "awesomeID", sig.getId() );
        assertEquals( "datadata", sig.getSigData().toString() );
        assertEquals( StringExpression.makeString( "payload" ), sig.getPayload() );
        assertEquals( new ListExpression( "signature", "awesomeID", "datadata",
                "payload" ), sig.toASE() );
    }
}
