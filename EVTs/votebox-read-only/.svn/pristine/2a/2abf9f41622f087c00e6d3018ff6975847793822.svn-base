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

import sexpression.*;

/**
 * This layer handles signatures.
 * 
 * @author kyle
 * 
 */
public class AuditoriumIntegrityLayer extends AAuditoriumLayer {

    public static final ASExpression PATTERN = new ListExpression(
            StringExpression.makeString( "signed-message" ),
            Wildcard.SINGLETON, Wildcard.SINGLETON );

    private final String _nodeID;
    private final IKeyStore _keystore;
    private Cert _mycert;

    // / All certificate authority keys are expected to be annotated thusly
    public static final String CA_ANNOTATION = "ca";

    /**
     * @param child
     *            This new instance is a parent of this given instance.
     * @param host
     *            This is the host that is using this stack.
     * @param keystore
     *            This is the keystore to use for locating keys to perform cryptographic operations.
     */
    public AuditoriumIntegrityLayer(AAuditoriumLayer child,
            IAuditoriumHost host, IKeyStore keystore) {
        super( child, host );
        _nodeID = host.getNodeId();
        _keystore = keystore;

        if (keystore == null)
            Bugout
                    .msg( "warning: keystore is NULL in AuditoriumIntegrityLayer()" );

        try {
            init();
        }
        catch (Exception e) {
            throw new FatalNetworkException(
                    "Can't perform necessary cryptographic operations", e );
        }
    }

    /**
     * @see auditorium.IAuditoriumLayer#makeAnnouncement(sexpression.ASExpression)
     */
    public ASExpression makeAnnouncement(ASExpression datum) {
        // Make new datum
        ASExpression newdatum;

        try {
            newdatum = new ListExpression( StringExpression
                    .makeString( "signed-message" ), _mycert.toASE(),
                    RSACrypto.SINGLETON.sign( datum, _keystore.loadKey( _nodeID ) )
                            .toASE() );
        }
        catch (AuditoriumCryptoException e) {
            throw new FatalNetworkException(
                    "Couldn't make an announcement because of a crypto error.",
                    e );
        }

        // Decorated method call.
        return getChild().makeAnnouncement( newdatum );
    }

    /**
     * @see auditorium.IAuditoriumLayer#makeJoin(sexpression.ASExpression)
     */
    public ASExpression makeJoin(ASExpression datum) {
        return getChild().makeJoin( datum );
    }

    /**
     * @see auditorium.IAuditoriumLayer#makeJoinReply(sexpression.ASExpression,
     *      sexpression.ASExpression)
     */
    public ASExpression makeJoinReply(ASExpression datum) {
        return getChild().makeJoinReply( datum );
    }

    /**
     * @see auditorium.IAuditoriumLayer#receiveAnnouncement(sexpression.ASExpression)
     */
    public ASExpression receiveAnnouncement(ASExpression datum)
            throws IncorrectFormatException {
        try {
            // Decorated method call
            ASExpression matchresult = PATTERN.match( getChild()
                    .receiveAnnouncement( datum ) );
            if (matchresult == NoMatch.SINGLETON)
                throw new IncorrectFormatException( datum, new Exception( datum
                        + " doesn't match the pattern:" + PATTERN ) );
            ListExpression matchlist = (ListExpression) matchresult;

            Cert cer = new Cert( matchlist.get( 0 ) );
            Signature sig = new Signature( matchlist.get( 1 ) );
            RSACrypto.SINGLETON.verify( new Signature( matchlist.get( 1 ) ),
                new Cert( matchlist.get( 0 ) ) );

            String signingKeyId = cer.getSignature().getId(); // the ID of the key that signed the *certificate*
            Cert signingCert = _keystore.loadCert( signingKeyId ); // the cert that signed the certificate
            if (signingCert.getKey().getAnnotation().equals( CA_ANNOTATION )) {
            	// verify that the signature on the certificate itself is correct
                RSACrypto.SINGLETON.verify( cer.getSignature(), signingCert );
            }
            else {
            	throw new SignerValidityException("Certificate on message signature was signed by non-authoritative key '"
                        + signingKeyId + "' (annotation: '"
                        + signingCert.getKey().getAnnotation() + "')");
            }

            // Send the rest upwards.
            return sig.getPayload();
        }
        catch (AuditoriumCryptoException e) {
            throw new IncorrectFormatException( datum, e );
        } catch (SignerValidityException e) {
			throw new IncorrectFormatException( datum, e );
		}
    }

    /**
     * @see auditorium.IAuditoriumLayer#receiveJoinReply(sexpression.ASExpression)
     */
    public ASExpression receiveJoinReply(ASExpression datum)
            throws IncorrectFormatException {
        return getChild().receiveJoinReply( datum );
    }

    /**
     * @see auditorium.IAuditoriumLayer#receiveJoin(sexpression.ASExpression)
     */
    public ASExpression receiveJoin(ASExpression datum)
            throws IncorrectFormatException {
        return datum;
    }

    /**
     * Run some initial tests to make sure that this host can do all the
     * cryptographic things it needs to be able to do.
     */
    private void init() throws Exception {
        StringExpression message = StringExpression.makeString( "test" );

        // load my cert
        _mycert = _keystore.loadCert( _nodeID );

        // Make a test signature and verify it. (Check that "my" cert and key
        // are on disk)
        Signature sig = RSACrypto.SINGLETON.sign( message, _keystore
                .loadKey( _nodeID ) );
        RSACrypto.SINGLETON.verify( sig, _mycert );
    }
}
