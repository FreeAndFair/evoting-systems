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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import auditorium.Key;

/**
 * This class implements an El Gamal encryption key-pair, which can then be used
 * (factory style) to encrypt or decrypt messages.
 * 
 * @author dwallach
 * 
 */

public class ElGamalCrypto {

    public static final ElGamalCrypto SINGLETON = new ElGamalCrypto();

    // this generator and modulus were generated through Modulus.main() and
    // consumed 7 minutes of CPU on a 2GHz Core 2 Duo iMac. random memeber
    // (derived from mod/2) - this will be used to get the additive property out
    // of doing multiplication.
    private static final String GENERATOR_STRING = "2016433053757341104328548369260225448420178492488839339195079012913740203550581367917603578255836416301659447919134003412324535550203014660828445101581073366209571738168074363709988319601925328131931318253630428729995428849722161812181697865734851328186930582450521842890975960480674438455535966317209024008129126238043911181175493403751902643934946891633427176473184689859908734305925529262343808427749985844869145540026953651663690952752846237422048321944844544";
    private static final String MOD_STRING = "4008068760601560176181090811191269958616134140815365887701703622467302386397406595276102404102599183050725940409230956564362213996772507892182603738589047156399535390756432494533344022585855134419330844861393164590002967760368498512584631894520092843017130932721913480603013976030676448835771942383177369284649842316969774775111437516174141766494812679525434402192524629913006391105583246025610804250839276542776846098833535690824388875515507421677606470210284503";
    private static final String MEMBER_STRING = "2004034380300780088090545405595634979308067070407682943850851811233651193198703297638051202051299591525362970204615478282181106998386253946091301869294523578199767695378216247266672011292927567209665422430696582295001483880184249256292315947260046421508565466360956740301506988015338224417885971191588684642324921158484887387555718758087070883247406339762717201096262314956503195552791623012805402125419638271388423049416767845412194437757753710838803235105142251";
    private static final int NUM_PRIME_BITS = 1536;
    private static final int PRIME_CONFIDENCE = 80;

    // These annotations will go in generated public and private ElGamal keys.
    private static final String PRIVATE_ANNOTATION = "ElGamalPrivate";
    private static final String PUBLIC_ANNOTATION = "ElGamalPublic";

    // Precompute this many values for the member table (0 for now..)
    private static final int TABLE_SIZE = 0;

    // Member fields
    private final Modulus _modulusCls;
    private final BigInteger _mod;
    private final BigInteger _gen;
    private final BigInteger _member;
    private final HashMap<BigInteger, BigInteger> _map;
    private final ArrayList<BigInteger> _lastRandom;

    private ElGamalCrypto() {
        _modulusCls = new Modulus(NUM_PRIME_BITS, PRIME_CONFIDENCE,
                GENERATOR_STRING, MOD_STRING);
        _mod = _modulusCls.getModulus();
        _gen = _modulusCls.getGenerator();
        _member = new BigInteger(MEMBER_STRING);
        _map = new HashMap<BigInteger, BigInteger>();
        _lastRandom = new ArrayList<BigInteger>();
        initMap();
    }

    private void initMap() {
        for (int lcv = 0; lcv < TABLE_SIZE; lcv++) {
            BigInteger blcv = new BigInteger(Integer.toString(lcv));
            _map.put(_member.modPow(blcv, _mod), blcv);
        }
    }

    /**
     * Generate a new ElGamal key pair.
     * 
     * @param id
     *            Identify the generated key pair with this string. (Generated
     *            key instances will have their id fields set to this value).
     * @return This method returns a new key pair where the keys are arranged
     *         (public,private)
     */
    public Pair<Key> generate(String id) {
        Key privateKey = new Key(id, PRIVATE_ANNOTATION, _mod, _modulusCls
                .getRandomValue());
        Key publicKey = new Key(id, PUBLIC_ANNOTATION, _mod, _gen.modPow(
                privateKey.getKey(), _mod));
        return new Pair<Key>(publicKey, privateKey);
    }

    /**
     * Perform an encryption.
     * 
     * @param key
     *            Encrypt with this key (should be generated by generate())
     * @param plainText
     *            Encrypt this plaintext.
     * @return This method returns an ElGamal cipher Pair.
     */
    public Pair<BigInteger> encrypt(Key key, BigInteger plainText) {
        if (plainText.compareTo(_mod) >= 0)
            throw new RuntimeException(
                    "Plaintext cannot be larger than modulus");

        BigInteger rnd = _modulusCls.getRandomValue();
        BigInteger c1 = _gen.modPow(rnd, _mod);
        BigInteger c2 = _member.modPow(plainText, _mod).multiply(
                key.getKey().modPow(rnd, _mod)).mod(_mod);
        _lastRandom.add(rnd);
        return new Pair<BigInteger>(c1, c2);
    }

    /**
     * Perform a normal decryption.
     * 
     * @param key
     *            Decrypt with this key. (should be generated by generate())
     * @param cipherText
     *            Decrypt this cipher (should be generated by encrypt())
     * @return This method returns the
     */
    public BigInteger decrypt(Key key, Pair<BigInteger> cipherText) {
        return lookup(cipherText.get2().multiply(
                cipherText.get1().modPow(key.getKey(), _mod).modInverse(_mod))
                .mod(_mod));
    }

    /**
     * Perform a decryption without the decryption key, but with the randomness
     * from the encryption
     * 
     * @param r - random value used for encrypt
     * @param cipherText - cipherText
     * @param publickey - public counterpart of the private key used for encrypt
     * 
     * @return the plain text
     */
    public BigInteger decrypt(BigInteger r, Key publickey,
            Pair<BigInteger> cipherText) {
        return lookup(cipherText.get2().multiply(
                publickey.getKey().modPow(r, _mod).modInverse(_mod)).mod(_mod));
    }

    private BigInteger lookup(BigInteger i) {
        if (_map.containsKey(i))
            return _map.get(i);
        else
            for (int lcv = TABLE_SIZE; true; lcv++) {
                BigInteger blcv = new BigInteger(Integer.toString(lcv));
                if (_member.modPow(blcv, _mod).equals(i))
                    return blcv;
            }
    }

    /**
     * @return This method returns the most recent randomness used by the
     *         encrypt method.
     */
    public List<BigInteger> getRecentRandomness() {
        return new ArrayList<BigInteger>(_lastRandom);
    }

    /**
     * Forget about the most recent randomness used by the encrypt method.
     */
    public void clearRecentRandomness() {
        _lastRandom.clear();
    }

    /**
     * homomorphic multiplication of ciphertext tuples - does not modify
     * arguments. mult(encrypt(a), encrypt(b)) = encrypt(a * b)
     */
    public Pair<BigInteger> mult(Pair<BigInteger> a, Pair<BigInteger> b) {
        return new Pair<BigInteger>(a.get1().multiply(b.get1()).mod(_mod), a
                .get2().multiply(b.get2()).mod(_mod));
    }
}
