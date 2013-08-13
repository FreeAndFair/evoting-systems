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

import java.io.File;
import java.io.FileOutputStream;
import java.security.KeyPair;
import java.security.KeyPairGenerator;
import java.security.NoSuchAlgorithmException;
import java.security.interfaces.RSAPrivateKey;
import java.security.interfaces.RSAPublicKey;

import sexpression.*;
import sexpression.stream.*;

/**
 * Use an instance of this class to generate RSA keys. It's main method will
 * generate a set of keys, all signed by the same CA key (which it will also
 * generate).
 * 
 * @author kyle
 * 
 */
public class Generator {

    /**
     * A public/private key pair. This class is used by the generator to wrap
     * the generated return value.
     */
    public static class Keys {

        private final Key _public;
        private final Key _private;

        /**
         * @param pub
         *            This is the public key for the pair.
         * @param priv
         *            This is the private key for the pair.
         */
        public Keys(Key pub, Key priv) {
            _public = pub;
            _private = priv;
        }

        /**
         * @return Get this pair's public part.
         */
        public Key getPublic() {
            return _public;
        }

        /**
         * @return Get this pair's private part.
         */
        public Key getPrivate() {
            return _private;
        }
    }

    public static final String FORMAT = "Can't parse arguments:\n"
            + "[0] is the number of keys you'd like to generate.\n"
            + "[1] is where you want to throw them.";

    /**
     * @param args
     *            [0] is the number of keys you'd like to generate. [1] is where
     *            you want to throw them.
     */
    public static void main(String... args) throws Exception {
        // parse args
        if (args.length != 2) {
            System.err.println( FORMAT );
            return;
        }
        int numkeys;
        try {
            numkeys = Integer.parseInt( args[0] );
        }
        catch (NumberFormatException e) {
            System.err.println( "BAD NUMBER!" );
            System.err.println( FORMAT );
            return;
        }
        File outdir = new File( args[1] );
        if (!outdir.isDirectory() && outdir.canWrite() && outdir.canRead()) {
            System.err.println( "BAD DIRECTORY!" );
            System.err.println( FORMAT );
        }

        Generator gen = new Generator();

        // generate a key for the CA.
        Keys cakeys = gen.generateKey( "ca", "ca" );
        Cert cacert = new Cert( RSACrypto.SINGLETON.sign( cakeys.getPublic()
                .toASE(), cakeys.getPrivate() ) );
        write( cakeys.getPrivate().toASE(), outdir.getPath() + File.separator
                + "ca.key" );
        write( cacert.toASE(), outdir.getPath() + File.separator + "ca.cert" );

        // generate numkeys keys and write them to files.
        for (int lcv = 0; lcv < numkeys; lcv++) {
            Keys keys = gen.generateKey( Integer.toString( lcv ), "booth" );
            Cert cert = new Cert( RSACrypto.SINGLETON.sign( keys.getPublic()
                    .toASE(), cakeys.getPrivate() ) );
            write( keys.getPrivate().toASE(), outdir.getPath() + File.separator
                    + Integer.toString( lcv ) + ".key" );
            write( cert.toASE(), outdir.getPath() + File.separator
                    + Integer.toString( lcv ) + ".cert" );
        }
    }

    private static void write(ASExpression exp, String abspath)
            throws Exception {
        File f = new File( abspath );
        new ASEWriter( new FileOutputStream( f ) ).writeASE( exp );
    }

    private final KeyPairGenerator _generator;

    public Generator() {
        try {
            _generator = KeyPairGenerator.getInstance( "RSA" );
        }
        catch (NoSuchAlgorithmException e) {
            throw new RuntimeException( "problem creating generator", e );
        }
    }

    /**
     * Generate a key pair.
     * 
     * @param id
     *            The pair will be assigned to the host with this ID.
     * @param annotation
     *            Annotate the key with this string. (This field is used for
     *            capability assignement).
     * @return This method returns the generated key pair.
     */
    public Keys generateKey(String id, String annotation) {
        KeyPair kp = _generator.generateKeyPair();
        RSAPublicKey pub = (RSAPublicKey) kp.getPublic();
        RSAPrivateKey priv = (RSAPrivateKey) kp.getPrivate();
        return new Keys( new Key( id, annotation, pub.getModulus(), pub
                .getPublicExponent() ), new Key( id, annotation, priv
                .getModulus(), priv.getPrivateExponent() ) );
    }

    /**
     * Create a certificate (a signed key).
     * 
     * @param signer
     *            This is the key of the signer of the certificate.
     * @param signee
     *            This is the key that will be signed and placed into the
     *            certificate.
     * @return This method returns the created certificate.
     * @throws AuditoriumCryptoException
     *             This method throws if there are platform issues preventing
     *             the signature from happening.
     */
    public Cert createCert(Key signer, Key signee)
            throws AuditoriumCryptoException {
        try {
            return new Cert( RSACrypto.SINGLETON.sign( signee.toASE(), signer ) );
        }
        catch (IncorrectFormatException e) {
            throw new RuntimeException(
                    "signed key was found to not actually have a key", e );
        }
    }
}
