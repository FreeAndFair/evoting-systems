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

import java.security.KeyFactory;
import java.security.PrivateKey;
import java.security.PublicKey;
import java.security.spec.RSAPrivateKeySpec;
import java.security.spec.RSAPublicKeySpec;

import sexpression.*;

/**
 * Crypto primitives used in auditorium are wrapped here.
 * 
 * @author kyle
 * 
 */
public class RSACrypto {

    public static final RSACrypto SINGLETON = new RSACrypto();

    private RSACrypto() {}

    /**
     * Create an RSA digital signature.
     * 
     * @param data
     *            Sign this expression's verbatim form.
     * @param key
     *            Use this key to create the signature.
     * @return This method returns the signature data.
     */
    public Signature sign(ASExpression data, Key key)
            throws AuditoriumCryptoException {
        try {
            KeyFactory factory = KeyFactory.getInstance( "RSA" );
            java.security.Signature sig = java.security.Signature
                    .getInstance( "SHA1withRSA" );
            PrivateKey privkey = factory
                    .generatePrivate( new RSAPrivateKeySpec( key.getMod(), key
                            .getKey() ) );
            sig.initSign( privkey );
            sig.update( data.toVerbatim() );
            return new Signature( key.getId(),
                    StringExpression.makeString( sig.sign() ), data );
        }
        catch (Exception e) {
            throw new AuditoriumCryptoException( "sign", e );
        }
    }

    /**
     * Verify that an RSA digital signature (possibly created by the sign
     * function) came from a particular host.
     * 
     * @param signature
     *            This is the digital signature, itself.
     * @param host
     *            This is the certificate of the host that supposedly signed the
     *            message.
     */
    public void verify(Signature signature, Cert host)
            throws AuditoriumCryptoException {
        try {
            KeyFactory factory = KeyFactory.getInstance( "RSA" );
            java.security.Signature sig = java.security.Signature
                    .getInstance( "SHA1withRSA" );
            PublicKey pubkey = factory.generatePublic( new RSAPublicKeySpec(
                    host.getKey().getMod(), host.getKey().getKey() ) );
            sig.initVerify( pubkey );
            sig.update( signature.getPayload().toVerbatim() );
            if (!sig.verify( signature.getSigData().getBytesCopy() ))
                throw new AuditoriumCryptoException( "verify signature",
                        new Exception( "Verification failure: " + signature
                                + " not signed by " + host ) );
        }
        catch (Exception e) {
            throw new AuditoriumCryptoException( "verify signature", e );
        }
    }
}
