package edu.uconn.cse.adder.plugin;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.StringTokenizer;

import edu.uconn.cse.adder.AdderInteger;
import edu.uconn.cse.adder.ElgamalCiphertext;
import edu.uconn.cse.adder.InvalidPublicKeyException;
import edu.uconn.cse.adder.Polynomial;
import edu.uconn.cse.adder.PrivateKey;
import edu.uconn.cse.adder.PublicKey;
import edu.uconn.cse.adder.Vote;
import edu.uconn.cse.adder.VoteProof;

/**
 * The adder plugin.
 *
 * @author David Walluck
 * @version $LastChangedRevision$ $LastChangedDate$
 * @since 0.0.1
 */
public final class Plugin {
    /** Don't instantiate me. */
    private Plugin() {

    }

    /**
     * Encrypts the given vote.
     *
     * @param key the key
     * @param vote the vote
     * @param min the minimum number of allowed choices
     * @param max the maximum number of allowed choices
     * @return the encrypted vote
     */
    public static String encryptVote(String key, String vote, int min,
                                     int max) {
        PublicKey pubKey = PublicKey.fromString(key);
        int c = vote.length();
        List/*<AdderInteger>*/ choices = new ArrayList/*<AdderInteger>*/(c);

        for (int i = 0; i < c; i++) {
            if (vote.charAt(i) == '0') {
                choices.add(AdderInteger.ZERO);
            } else if (vote.charAt(i) == '1') {
                choices.add(AdderInteger.ONE);
            }
        }

        Vote v = KeyManagement.encryptVote(pubKey, choices);

        VoteProof proof = new VoteProof();
        proof.compute(v, pubKey, choices, min, max);

        return v + ":" + proof;
    }

    /**
     * Creates a key pair.
     *
     * @param user the user
     * @param procedure the procedure
     * @param key the key
     * @param secure true if security is wanted
     * @return the key pair
     */
    public static boolean createKeyPair(String user, String procedure,
                                         String key, boolean secure) {
        PublicKey pubKey = PublicKey.fromString(key);

        return KeyManagement.createKeyPair(user, procedure, pubKey);
    }

    /**
     * Decrypts the final vote.
     *
     * @param user the user
     * @param procedure the procedure
     * @param voteString the vote string
     * @return the final vote
     */
    public static String decryptSum(String user, String procedure,
                                    String voteString) {
        return KeyManagement.decryptSum(user, procedure,
                                        Vote.fromString(voteString));
    }

    /**
     * Reads the public key.
     *
     * @param user the user
     * @param procedure the procedure
     * @return the public key
     * @throws InvalidPublicKeyException
     */
    public static String readPubKey(String user, String procedure) {
        return KeyManagement.readPubKey(user, procedure).toString();
    }

    /**
     * Reads the private key.
     *
     * @param user the user
     * @param procedure the procedure
     * @return the private key
     */
    public static String readPrivKey(String user, String procedure) {
        try {
            return KeyManagement.readPrivKey(user, procedure).toString();
        } catch (FileNotFoundException fnfe) {
            return null;
        } catch (IOException ioe) {
            return null;
        }
    }

    /**
     * Writes the private key.
     *
     * @param user the user
     * @param procedure the procedure
     * @param key the key
     * @return true if the private key was written successfully
     */
    public static boolean writePrivKey(String user, String procedure,
                                       String key) {
        return KeyManagement.writePrivKey(user, procedure, key);
    }

    /**
     * Reads the second private key.
     *
     * @param user the user
     * @param procedure the procedure
     * @return the second private key
     */
    public static String readPrivKey2(String user, String procedure) {
        try {
            return KeyManagement.readPrivKey2(user, procedure).toString();
        } catch (FileNotFoundException fnfe) {
            return null;
        } catch (IOException ioe) {
            return null;
        }
    }

    /**
     * Writes the second private key.
     *
     * @param user to user
     * @param procedure the procedure
     * @param key the key
     * @return the second private key
     */
    public static boolean writePrivKey2(String user, String procedure,
                                        String key) {
        return KeyManagement.writePrivKey2(user, procedure, key);
    }

    private static List/*<String>*/ parsePrivKeys(String pubkeys) {
        List/*<String>*/ keys = new ArrayList/*<String>*/();
        StringTokenizer st = new StringTokenizer(pubkeys, "\n");

        while (st.hasMoreTokens()) {
            keys.add(st.nextToken());
        }

        return keys;
    }

    /**
     * Computes the secret key.
     *
     * @param user the user
     * @param procedure the procedure
     * @param values the values
     * @return the secret key
     */
    public static boolean computeSecretKey(String user, String procedure,
                                           String values) {
        List/*<String>*/ valueVs = parsePrivKeys(values);
        List/*<ElgamalCiphertext>*/ keyList
            = new  ArrayList/*<ElgamalCiphertext>*/(valueVs.size());

        /*for (String key : valueVs) {*/
        for (Iterator it = valueVs.iterator(); it.hasNext();) {
            String key = (String) it.next();
            keyList.add(ElgamalCiphertext.fromString(key));
        }

        PrivateKey privKey
            = PrivateKey.fromString(readPrivKey(user, procedure));
        PrivateKey finalKey = privKey.getFinalPrivKey(keyList);

        return writePrivKey2(user, procedure, finalKey.toString());
    }

    /**
     * Encrypts the <code>g</code> value.
     *
     * @param user the user
     * @param procedure the procedure
     * @return the encrypted <code>g</code> value
     */
    public static String encryptGValue(String user, String procedure) {
        StringBuffer sb = new StringBuffer(4096);

        try {
            Polynomial poly = KeyManagement.readPoly(user, procedure);
            KeyManagement.deletePoly(user, procedure);

            int size = poly.getCoeffs().size();

            for (int i = 0; i < size; i++) {
                sb.append(i);
                sb.append(" ");
                sb.append(poly.getG().pow((AdderInteger) poly.getCoeffs()
                                                             .get(i)));
                sb.append("\n");
            }
        } catch (FileNotFoundException fnfe) {
            return null;
        } catch (IOException ioe) {
            return null;
        }

        return sb.toString();
    }

    /**
     * Computes the short hash of the given vote.
     *
     * @param voteString the vote string
     * @return the short hash of the given vote
     */
    public static String shortHash(String voteString) {
        return KeyManagement.shortHash(Vote.fromString(voteString));
    }

    private static List/*<String>*/ parsePubKeys(String pubKeys) {
        List/*<String>*/ keys = new ArrayList/*<String>*/();
        StringTokenizer st = new StringTokenizer(pubKeys, "\n");

        while (st.hasMoreTokens()) {
            String key = st.nextToken();
            keys.add(key);
        }

        return keys;
    }

    /**
     * Encrypts the polynomial.
     *
     * @param user the user
     * @param procedure the procedure
     * @param pubKeysStr the public keys string
     * @param d the degree
     * @return the encrypted polynomial
     */
    public static String encryptPoly(String user, String procedure,
                                     String pubKeysStr, int d) {
        String pubKeyStr = KeyManagement.readPubKey(user, procedure).toString();
        PublicKey pubKey = PublicKey.fromString(pubKeyStr);

        Polynomial poly = new Polynomial(pubKey.getP(), pubKey.getG(),
                                         pubKey.getF(), d - 1);

        KeyManagement.writePolynomial(user, procedure, poly.toString());

        List/*<String>*/ pubKeys = parsePubKeys(pubKeysStr);

        StringBuffer sb = new StringBuffer(4096);

        /*for (String keyStr : pubKeys) {*/
        for (Iterator it = pubKeys.iterator(); it.hasNext();) {
            String keyStr = (String) it.next();

            try {
                StringTokenizer st = new StringTokenizer(keyStr, " ");
                String auth = st.nextToken();
                String realKeyStr = st.nextToken();
                PublicKey key = PublicKey.fromString(realKeyStr);
                ElgamalCiphertext vote
                    = key.encryptPoly(poly.evaluate(new
                                                    AdderInteger(auth,
                                                                 key.getQ())));

                sb.append(auth);
                sb.append(" ");
                sb.append(vote.toString());
                sb.append("\n");
            } catch (NoSuchElementException nsee) {
                throw new InvalidPublicKeyException(nsee.getMessage());
            }
        }

        return sb.toString();
    }
}
