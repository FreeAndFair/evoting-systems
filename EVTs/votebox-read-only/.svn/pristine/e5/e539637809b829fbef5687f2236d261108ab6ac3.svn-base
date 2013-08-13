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

import org.junit.*;

import sexpression.*;
import auditorium.*;
import auditorium.Generator.Keys;

public class IntegrityLayerTest {

    // Stuff we're testing
    private IAuditoriumHost _host = new IAuditoriumHost() {

        public ASExpression getAddresses() {
            throw new RuntimeException( "unused" );
        }

        public Log getLog() {
            throw new RuntimeException( "unused" );
        }

        public HostPointer getMe() {
            throw new RuntimeException( "unused" );
        }

        public String getNodeId() {
            return "TEST";
        }

        public void receiveAnnouncement(Message message) {
            throw new RuntimeException( "unused" );
        }

        public void removeLink(Link link) {
            throw new RuntimeException( "unused" );
        }

        public String nextSequence() {
            return "TEST";
        }
    };
    private Cert _mycert;
    private Key _mykey;
    private Cert _cacert;
    private IKeyStore _keystore = new IKeyStore() {

        public Cert loadCert(String nodeid) throws AuditoriumCryptoException {
            if (nodeid.equals("ca"))
                return _cacert;
            return _mycert;
        }

        public Key loadKey(String nodeid) throws AuditoriumCryptoException {
            return _mykey;
        }
        
        public Object loadAdderKey(String nodeid) throws RuntimeException{
        	return null;
        }
    };
    private AuditoriumIntegrityLayer _layer;

    @Before
    public void build() throws Exception {
        Generator gen = new Generator();
        Keys ca = gen.generateKey( "ca", "ca" );
        Keys my = gen.generateKey( "me", "booth" );
        _mykey = my.getPrivate();
        _mycert = new Cert( RSACrypto.SINGLETON.sign( my.getPublic().toASE(), ca
                .getPrivate() ) );
        _cacert = new Cert( RSACrypto.SINGLETON.sign( ca.getPublic().toASE(), ca
                .getPrivate() ) );
        _layer = new AuditoriumIntegrityLayer( AAuditoriumLayer.BOTTOM, _host,
                _keystore );
    }

    // ** makeAnnouncement(ASExpression) tests **
    private void make_announcement_test(ASExpression datum) throws Exception {
        // compute actual
        ASExpression wrapped = _layer.makeAnnouncement( datum );

        // compute expected
        ASExpression matchagainst = new ListExpression( StringExpression
                .makeString( "signed-message" ), _mycert.toASE(),
                RSACrypto.SINGLETON.sign( datum, _mykey ).toASE() );

        assertEquals( matchagainst, wrapped );

    }

    @Test
    public void makeAnnouncement_1() throws Exception {
        make_announcement_test( NoMatch.SINGLETON );
    }

    @Test
    public void makeAnnouncement_2() throws Exception {
        make_announcement_test( Nothing.SINGLETON );
    }

    @Test
    public void makeAnnouncement_3() throws Exception {
        make_announcement_test( StringExpression.EMPTY );
    }

    @Test
    public void makeAnnouncement_4() throws Exception {
        make_announcement_test( ListExpression.EMPTY );
    }

    @Test
    public void makeAnnouncement_5() throws Exception {
        make_announcement_test( StringExpression.makeString( "TEST" ) );
    }

    @Test
    public void makeAnnouncement_6() throws Exception {
        make_announcement_test( new ListExpression( StringExpression
                .makeString( "TEST" ), StringExpression.makeString( "TEST" ) ) );
    }

    // ** receiveAnnouncement(ASExpression) tests **
    private void receive_announcement_test(ASExpression wrapthis)
            throws Exception {
        ASExpression wrapped = _layer.makeAnnouncement( wrapthis );
        System.err.println( wrapped );
        assertEquals( wrapthis, _layer.receiveAnnouncement( wrapped ) );
    }

    private void receive_announcement_test_fail(ASExpression sendthis)
            throws IncorrectFormatException {
        _layer.receiveAnnouncement( sendthis );
    }

    // Good (actually construct a message with makeAnnouncement)
    @Test
    public void receive_announcement_1() throws Exception {
        receive_announcement_test( StringExpression.EMPTY );
    }

    @Test
    public void receive_announcement_2() throws Exception {
        receive_announcement_test( ListExpression.EMPTY );
    }

    @Test
    public void receive_announcement_3() throws Exception {
        receive_announcement_test( StringExpression.makeString( "Test" ) );
    }

    @Test
    public void receive_announcement_4() throws Exception {
        receive_announcement_test( new ListExpression( StringExpression
                .makeString( "Test" ) ) );
    }

    @Test
    public void receive_announcement_5() throws Exception {
        receive_announcement_test( new ListExpression( StringExpression
                .makeString( "Test" ), new ListExpression( StringExpression
                .makeString( "Test" ) ), StringExpression.makeString( "TEST" ) ) );
    }

    // Bad (random stuff)
    @Test(expected = IncorrectFormatException.class)
    public void receive_announcement_6() throws Exception {
        receive_announcement_test_fail( NoMatch.SINGLETON );
    }

    @Test(expected = IncorrectFormatException.class)
    public void receive_announcement_7() throws Exception {
        receive_announcement_test_fail( Nothing.SINGLETON );
    }

    @Test(expected = IncorrectFormatException.class)
    public void receive_announcement_8() throws Exception {
        receive_announcement_test_fail( StringExpression.EMPTY );
    }

    @Test(expected = IncorrectFormatException.class)
    public void receive_announcement_9() throws Exception {
        receive_announcement_test_fail( ListExpression.EMPTY );
    }

    @Test(expected = IncorrectFormatException.class)
    public void receive_announcement_10() throws Exception {
        receive_announcement_test_fail( StringExpression.makeString( "TEST" ) );
    }

    // Bad (format the message correctly, but make the cert, sig, or message
    // type not check) (Don't need to check with every single cert/key anymore).

    @Test(expected = IncorrectFormatException.class)
    public void receive_announcement_11() throws Exception {
        ASExpression datum = StringExpression.makeString( "TEST" );
        Signature sig = RSACrypto.SINGLETON.sign( datum, _mykey );

        _layer.receiveAnnouncement( new ListExpression( StringExpression
                .makeString( "not-signed-message" ), _mycert.toASE(), sig
                .toASE(), datum ) );
    }

    @Test(expected = IncorrectFormatException.class)
    public void receive_announcement_12() throws Exception {
        ASExpression datum = StringExpression.makeString( "TEST" );
        Signature sig = RSACrypto.SINGLETON.sign( datum, _mykey );
        byte[] sigbytes = sig.getSigData().getBytesCopy();
        sigbytes[0] = 1;
        Signature notsig = new Signature( "TEST", StringExpression
                .makeString( sigbytes ), datum );

        _layer.receiveAnnouncement( new ListExpression( StringExpression
                .makeString( "signed-message" ), _mycert.toASE(), notsig
                .toASE(), datum ) );
    }

    @Test(expected = IncorrectFormatException.class)
    public void receive_announcement_13() throws Exception {
        ASExpression datum = StringExpression.makeString( "TEST" );

        _layer.receiveAnnouncement( new ListExpression( StringExpression
                .makeString( "signature" ), _mycert.toASE(),
                StringExpression.EMPTY, datum ) );
    }

    // ** do nothing method tests **
    // (all these tested methods essentially return what they're given)
    private void donothing_test(ASExpression datum) throws Exception {
        for (int lcv = 1; lcv <= 10; lcv++) {
            assertEquals( datum, _layer.makeJoin( datum ) );
            assertEquals( datum, _layer.makeJoinReply( datum ) );
            assertEquals( datum, _layer.receiveJoin( datum ) );
            assertEquals( datum, _layer.receiveJoinReply( datum ) );
        }
    }

    @Test
    public void donothing_1() throws Exception {
        donothing_test( NoMatch.SINGLETON );
    }

    @Test
    public void donothing_2() throws Exception {
        donothing_test( Nothing.SINGLETON );
    }

    @Test
    public void donothing_3() throws Exception {
        donothing_test( StringExpression.EMPTY );
    }

    @Test
    public void donothing_4() throws Exception {
        donothing_test( ListExpression.EMPTY );
    }

    @Test
    public void donothing_5() throws Exception {
        donothing_test( StringExpression.makeString( "TEST" ) );
    }
}
