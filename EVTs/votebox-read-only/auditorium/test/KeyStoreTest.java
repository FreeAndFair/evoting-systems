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

import java.io.File;

import org.junit.*;

import auditorium.*;
import sexpression.*;

public class KeyStoreTest {

    private final ASExpression _message = new ListExpression( "one", "two" );

    private File _file;
    private SimpleKeyStore _keystore;

    @Before
    public void build() throws Exception {
        _file = new File( "tmp/" );
        _file.mkdir();
        Generator.main( "5", "tmp/" );
        _keystore = new SimpleKeyStore( "tmp/" );
    }

    @After
    public void tear() throws Exception {
        for (File child : _file.listFiles())
            child.delete();
        _file.delete();
    }

    @Test
    public void load_key() throws Exception {
        for (int lcv = 0; lcv < 5; lcv++) {
            Cert cert = _keystore.loadCert( Integer.toString( lcv ) );
            Key key = _keystore.loadKey( Integer.toString( lcv ) );
            Signature sig = RSACrypto.SINGLETON.sign( _message, key );
            RSACrypto.SINGLETON.verify( sig, cert );
        }
    }

    @Test(expected = AuditoriumCryptoException.class)
    public void load_key_fail_1() throws Exception {
        _keystore.loadKey( "blah" );
    }

    @Test(expected = AuditoriumCryptoException.class)
    public void load_key_fail_2() throws Exception {
        _keystore.loadKey( "5" );
    }

    @Test(expected = AuditoriumCryptoException.class)
    public void load_cert_fail_1() throws Exception {
        _keystore.loadCert( "blah" );
    }

    @Test(expected = AuditoriumCryptoException.class)
    public void load_cert_fail_2() throws Exception {
        _keystore.loadCert( "5" );
    }
}
