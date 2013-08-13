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

import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.math.BigInteger;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import edu.uconn.cse.adder.AdderInteger;
import edu.uconn.cse.adder.Election;
import edu.uconn.cse.adder.ElgamalCiphertext;
import edu.uconn.cse.adder.PrivateKey;
import edu.uconn.cse.adder.PublicKey;
import edu.uconn.cse.adder.Vote;
import edu.uconn.cse.adder.VoteProof;

import auditorium.Bugout;
import auditorium.Key;

import sexpression.*;
import votebox.crypto.interop.AdderKeyManipulator;
import votebox.middle.IBallotVars;
import votebox.middle.ballot.*;

public class BallotEncrypter {

    public static final BallotEncrypter SINGLETON = new BallotEncrypter();

    private List<BigInteger> _randomList;
    private ListExpression _recentBallot;
    
    private List<List<AdderInteger>> _adderRandom;

    private BallotEncrypter() {
    }

    /**
     * Takes an unencrypted ballot and encrypts it, while also generating a set of NIZKs to prove it is well formed.
     * 
     * @param ballot - Unencrypted ballot of the form ((race-id counter) ...) counter = {0, 1}
     * @param raceGroups - a list of of groups of race-ids that are considered "together" in a well formed ballot.
     * @param pubKey - the Adder PublicKey to use to encrypt the ballot and generate the NIZKs
     * @return a ListExpression in the form (((vote [vote]) (vote-ids ([id1], [id2], ...)) (proof [proof]) (public-key [key])) ...)
     */
    public ListExpression encryptWithProof(ListExpression ballot, List<List<String>> raceGroups, PublicKey pubKey){
    	_adderRandom = new ArrayList<List<AdderInteger>>();
    	List<ASExpression> subBallots = new ArrayList<ASExpression>();
    	
    	Map<String, ListExpression> ballotMap = new HashMap<String, ListExpression>();
    	for(int i = 0; i < ballot.size(); i++){
    		ListExpression vote = (ListExpression)ballot.get(i);
    		String id = vote.get(0).toString();
    		ballotMap.put(id, vote);
    	}
    	
    	for(List<String> group : raceGroups){
    		List<ASExpression> races = new ArrayList<ASExpression>();
    		for(String raceId : group)
    			races.add(ballotMap.get(raceId));
    		
    		ListExpression subBallot = new ListExpression(races);
    		subBallots.add(encryptSublistWithProof(subBallot, pubKey));
    	}
    	
    	_recentBallot = new ListExpression(subBallots);
    	
    	return _recentBallot;
    }
    
    /**
     * Take an unencryped ballot and make it encrypted, while also generating a NIZK.
     * 
     * @param ballot 
     *          This is the pre-encrypt ballot in the form ((race-id counter) ...)
     * @param publicKey
     *          this is an Adder-style public key
     * @return An ListExpression of the form ((vote [vote]) (vote-ids ([id1], [id2], ...)) (proof [proof]) (public-key [key]))
     */
    @SuppressWarnings("unchecked")
	public ListExpression encryptSublistWithProof(ListExpression ballot, PublicKey pubKey){
    	List<AdderInteger> value = new ArrayList<AdderInteger>();
    	List<ASExpression> valueIds = new ArrayList<ASExpression>();
    	
    	for(int i = 0; i < ballot.size(); i++){
    		ListExpression choice = (ListExpression)ballot.get(i);
    		value.add(new AdderInteger(choice.get(1).toString()));
    		valueIds.add(choice.get(0));
    	}//for
    	
    	PublicKey finalPubKey = AdderKeyManipulator.generateFinalPublicKey(pubKey);
		
		Vote vote = finalPubKey.encrypt(value);
		
		List<ElgamalCiphertext> ciphers = (List<ElgamalCiphertext>)vote.getCipherList();
		
		List<AdderInteger> subRandom = new ArrayList<AdderInteger>();
		for(ElgamalCiphertext cipher : ciphers)
			subRandom.add(cipher.getR());
		
		_adderRandom.add(subRandom);
		
		VoteProof proof = new VoteProof();
		proof.compute(vote, finalPubKey, value, 0, 1);
    	
		ListExpression vList = new ListExpression(StringExpression.makeString("vote"),
				//StringExpression.makeString(vote.toString()));
				vote.toASE());
		ListExpression idList = new ListExpression(StringExpression.makeString("vote-ids"),
				new ListExpression(valueIds));
		ListExpression pList = new ListExpression(StringExpression.makeString("proof"),
				//StringExpression.makeString(proof.toString()));
				proof.toASE());
		ListExpression kList = new ListExpression(StringExpression.makeString("public-key"),
				//StringExpression.makeString(finalPubKey.toString()));
				finalPubKey.toASE());
		
		ListExpression ret = new ListExpression(vList, idList, pList, kList);
		
		return ret;
    }
    
    /**
     * Take an unencrypted ballot form and make it encrypted.
     * 
     * @param ballot
     *            This is the pre-encrypt ballot in the form ((race-id
     *            counter)...)
     * @param publicKey
     * 			  this is the public ElGamal key used to encrypt the ballot
     * @return This method returns the encrypted form of ballot in the form
     *         ((race-id E(counter))...)
     */
    public ListExpression encrypt(ListExpression ballot, Key publicKey) {
    	ElGamalCrypto.SINGLETON.clearRecentRandomness();
        ArrayList<ASExpression> encryptedpairs = new ArrayList<ASExpression>();
        for (ASExpression ase : ballot) {
            ListExpression le = (ListExpression) ase;
            StringExpression id = (StringExpression) le.get(0);
            StringExpression count = (StringExpression) le.get(1);
            /*Pair<BigInteger> cipher = ElGamalCrypto.SINGLETON.encrypt(
                    publicKey, new BigInteger(count
                            .getBytes()));*/
            
            Pair<BigInteger> cipher = ElGamalCrypto.SINGLETON.encrypt(publicKey, new BigInteger(count.toString()));
            /*ASExpression cipherase = new ListExpression(StringExpression
                    .makeString(cipher.get1().toByteArray()), StringExpression
                    .makeString(cipher.get2().toByteArray()));*/
            ASExpression cipherase = new ListExpression(StringExpression.makeString(cipher.get1().toString()), 
            		StringExpression.makeString(cipher.get2().toString()));
            encryptedpairs.add(new ListExpression(id, cipherase));
        }
        _recentBallot = new ListExpression(encryptedpairs);
        _randomList = ElGamalCrypto.SINGLETON.getRecentRandomness();
        ElGamalCrypto.SINGLETON.clearRecentRandomness();
        return _recentBallot;
    }
    
    /**
     * Decrypt an Adder Election using a PrivateKey.
     * 
     * @param election
     * @param privKey
     * @return Decrypted results
     */
    @SuppressWarnings("unchecked")
	public List<AdderInteger> adderDecryptWithKey(Election election, PublicKey publicKey, PrivateKey privateKey){
    	PrivateKey finalPrivateKey = AdderKeyManipulator.generateFinalPrivateKey(publicKey, privateKey);
    	PublicKey finalPublicKey = AdderKeyManipulator.generateFinalPublicKey(publicKey);
    	
    	Vote cipherSum = election.sumVotes();
		List<AdderInteger> partialSum = (List<AdderInteger>)finalPrivateKey.partialDecrypt(cipherSum);
		AdderInteger coeff = new AdderInteger(0);

		List<List<AdderInteger>> partialSums = new ArrayList<List<AdderInteger>>();
		partialSums.add(partialSum);

		List<AdderInteger> coeffs = new ArrayList<AdderInteger>();
		coeffs.add(coeff);

		List<AdderInteger> results = election.getFinalSum(partialSums, coeffs, cipherSum, finalPublicKey);
		
		return results;
    }
    
    /**
     * Decrypt an Adder ballot using the random values.
     * 
     * @param ballot
     * @param rVals
     * @param publicKey
     * @return Decrypted ballot, of the form ((race-id [adder integer]) ...)
     */
    public ListExpression adderDecrypt(ListExpression ballot, List<List<AdderInteger>> rVals){
    	Map<String, Vote> idsToVote = new HashMap<String, Vote>();
    	Map<String, PublicKey> idsToPubKey = new HashMap<String, PublicKey>();
    	Map<String, List<AdderInteger>> idsToRs = new HashMap<String, List<AdderInteger>>();
    	Map<String, List<AdderInteger>> idsToDecrypted = new HashMap<String, List<AdderInteger>>();
    	
    	for(int i = 0; i < ballot.size(); i++){
    		ListExpression race = (ListExpression)ballot.get(i);
    		//Vote vote = Vote.fromString(((ListExpression)race.get(0)).get(1).toString());
    		Vote vote = Vote.fromASE(((ListExpression)race.get(0)).get(1));
    		ListExpression voteIds = (ListExpression)((ListExpression)race.get(1)).get(1);
    		//PublicKey finalPubKey = PublicKey.fromString(((ListExpression)race.get(3)).get(1).toString());
    		PublicKey finalPubKey = PublicKey.fromASE(((ListExpression)race.get(3)).get(1));
    		
    		idsToVote.put(voteIds.toString(), vote);
    		idsToRs.put(voteIds.toString(), rVals.get(i));
    		idsToPubKey.put(voteIds.toString(), finalPubKey);
    	}

    	for(String ids : idsToVote.keySet()){
    		Vote vote = idsToVote.get(ids);
    		List<AdderInteger> rs = idsToRs.get(ids);
    		PublicKey finalPubKey = idsToPubKey.get(ids);
    		
    		List<AdderInteger> d = adderDecryptSublist(vote, rs, finalPubKey);
    		
    		idsToDecrypted.put(ids, d);
    	}
    	
    	return toTraditionalFormat(idsToDecrypted);
    }
    
    private ListExpression toTraditionalFormat(Map<String, List<AdderInteger>> idsToPlaintext){
    	List<ASExpression> subLists = new ArrayList<ASExpression>();
    	
    	for(String ids : idsToPlaintext.keySet()){
    		List<StringExpression> idList = parseIds(ids.toString());
    		List<AdderInteger> plaintexts = idsToPlaintext.get(ids);

    		for(int i = 0; i < idList.size(); i++){
    			StringExpression id = (StringExpression)idList.get(i);
    			AdderInteger plaintext = plaintexts.get(i);
    			List<ASExpression> subList = new ArrayList<ASExpression>();
    			subList.add(id);
    			//subList.add(StringExpression.make(plaintext.toString()));
    			subList.add(plaintext.toASE());
    			subLists.add(new ListExpression(subList));
    		}
    	}
    	
    	return new ListExpression(subLists);
    }
    
    private List<StringExpression> parseIds(String ids){
    	String[] strs = ids.split(" ");
    	List<StringExpression> toRet = new ArrayList<StringExpression>();
    	
    	for(String str : strs){
    		toRet.add(StringExpression.makeString(str.replaceAll("\\(", "").replaceAll("\\)", "")));
    	}
    	
    	return toRet;
    }
    
    /**
     * Decrypt a single Adder vote using the provided random values.
     * 
     * @param vote
     * @param rVals
     * 
     * @return Decrypted vote as a list of integers
     */
    @SuppressWarnings("unchecked")
	public List<AdderInteger> adderDecryptSublist(Vote vote, List<AdderInteger> rVals, PublicKey key){
    	//Adder encrypt is of m (public initial g, p, h) [infered from code]
    	//                    m = {0, 1}
    	//                    g' = g^r
    	//                    h' = (h^r) * f^m
    	
    	//Quick decrypt (given r) [puzzled out by Kevin Montrose]
    	//                    confirm g^r = g'
    	//                    m' = (h' / (h^r))
    	//                    if(m' == f) m = 1
    	//                    if(m' == 1) m = 0
    	
    	List<ElgamalCiphertext> ciphers = (List<ElgamalCiphertext>)vote.getCipherList();
    	List<AdderInteger> ret = new ArrayList<AdderInteger>();
    	
    	int i = 0;
    	
    	for(ElgamalCiphertext cipher : ciphers){
    		AdderInteger r = rVals.get(i);
    		
    		AdderInteger gPrime = cipher.getG();
    		AdderInteger hPrime = cipher.getH();
    		
    		if(!key.getG().pow(r).equals(gPrime)){
    			Bugout.err("Random value does not correspond to ciphertext.");
    			return null;
    		}
    		
    		AdderInteger mPrime = hPrime.divide(key.getH().pow(r));
    		AdderInteger m = null;
    		
    		//Observe that m was 0 or 1, thus step must be either f or 1 respectively
    		if(mPrime.equals(AdderInteger.ONE)){
    			m = AdderInteger.ZERO;
    		}//if
    		
    		if(mPrime.equals(key.getF())){
    			m = AdderInteger.ONE;
    		}//if
    		
    		if(m == null){
    			Bugout.err("Expected intermediate step to be f or 1, found "+mPrime+"\n [f = "+key.getF()+"]");
    			return null;
    		}
    		
    		ret.add(m);
    		
    	    i++;
    	}
    	
    	return ret;
    }
    
    /**
     * Decrypt a ballot using the r-values (not the decryption key).
     * 
     * @param ballot
     *            This is the ballot, formatted ((race-id encrypted-counter)...)
     * @param rVals
     *            These are the r-values, formatted ((race-id r-value)...)
     * @param publicKey
     * 			   The necissary ElGamal public key.
     * @return This method returns the decrypted ballot, formatted ((race-id
     *         plaintext-counter)...)
     */
    public ListExpression decrypt(ListExpression ballot, ListExpression rVals, Key publicKey) {
        if (ballot.size() != rVals.size())
            throw new RuntimeException("sizes must match");
        if (Ballot.BALLOT_PATTERN.match(ballot) == NoMatch.SINGLETON)
            throw new RuntimeException("ballot incorrectly formatted");
        if (Ballot.BALLOT_PATTERN.match(rVals) == NoMatch.SINGLETON)
            throw new RuntimeException("r-vals incorrectly formatted");

        ArrayList<ASExpression> decryptedpairs = new ArrayList<ASExpression>(
                ballot.size());
        Iterator<ASExpression> ballotitr = ballot.iterator();
        Iterator<ASExpression> ritr = rVals.iterator();
        while (ballotitr.hasNext()) {
            ListExpression ballotnext = (ListExpression) ballotitr.next();
            ListExpression rnext = (ListExpression) ritr.next();

            if (!ballotnext.get(0).equals(rnext.get(0)))
                throw new RuntimeException(
                        "incorrect set of r-values: uids do not match");

            ASExpression uid = ballotnext.get(0);
            /*BigInteger r = new BigInteger(((StringExpression) rnext.get(1))
                    .getBytes());
            BigInteger cipher1 = new BigInteger(
                    ((StringExpression) ((ListExpression) ballotnext.get(1))
                            .get(0)).getBytes());
            BigInteger cipher2 = new BigInteger(
                    ((StringExpression) ((ListExpression) ballotnext.get(1))
                            .get(1)).getBytes());*/
            BigInteger r = new BigInteger(((StringExpression) rnext.get(1)).toString());
            BigInteger cipher1 = new BigInteger(((StringExpression) ((ListExpression)ballotnext.get(1)).get(0)).toString());
            BigInteger cipher2 = new BigInteger(((StringExpression) ((ListExpression)ballotnext.get(1)).get(1)).toString());
            
            Pair<BigInteger> cipher = new Pair<BigInteger>(cipher1, cipher2);
            BigInteger plaincounter = ElGamalCrypto.SINGLETON.decrypt(r,
                    publicKey, cipher);
            /*decryptedpairs.add(new ListExpression(uid, StringExpression
                    .makeString(plaincounter.toByteArray())));*/
            decryptedpairs.add(new ListExpression(uid, StringExpression
                    .makeString(plaincounter.toString())));
        }
        return new ListExpression(decryptedpairs);
    }

    /**
     * Get the most recent random list.
     * 
     * @return This method returns the random list in the form ((uid rvalue)...)
     */
    public ListExpression getRecentRandom() {
        ArrayList<ASExpression> pairs = new ArrayList<ASExpression>();

        Iterator<ASExpression> ballotitr = _recentBallot.iterator();
        Iterator<BigInteger> ritr = _randomList.iterator();

        while (ballotitr.hasNext()) {
            ListExpression ballotpair = (ListExpression) ballotitr.next();
            BigInteger r = ritr.next();
            pairs.add(new ListExpression(ballotpair.get(0), StringExpression
                    .makeString(r.toString())));
        }

        return new ListExpression(pairs);
    }

    /**
     * Get the most recent random, for the Adder encryption sub-system.
     * 
     * @return This method returns the random list used in the last call to encryptWithProof(...).
     */
    public List<List<AdderInteger>> getRecentAdderRandom(){
    	return _adderRandom;
    }
    
    /**
     * Get the result of the most recent encrypt call.
     * 
     * @return This method returns the most recent encryption.
     */
    public ListExpression getRecentEncryptedBallot() {
        return _recentBallot;
    }

    /**
     * Clear the state.
     */
    public void clear() {
        _recentBallot = null;
        _randomList = null;
        _adderRandom = new ArrayList<List<AdderInteger>>();
    }

    /**
     * I'm going to use this main as a sandbox for generating performance
     * numbers using this encryption, etc.
     * 
     * @param args
     */
    public static void main(String[] args) throws Exception {
        BallotParser parser = new BallotParser();
        Ballot b = parser.getBallot(new IBallotVars() {

            public String getBallotFile() {
                return "ballot.xml";
            }

            public String getBallotPath() {
                return "";
            }

            public URL getBallotSchema() {
                return getClass().getResource(
                        "/votebox/middle/schema/ballot_schema.xsd");

            }

            public String getLayoutFile() {
                return null;
            }

            public URL getLayoutSchema() {
                return null;
            }
        });

        ThreadMXBean t = ManagementFactory.getThreadMXBean();
        
        ListExpression b_count = (ListExpression) b.getCastBallot();
        
        ListExpression b_count_crypt = SINGLETON.encrypt(b_count, STATICKEY.SINGLETON.PUBLIC_KEY);
        ListExpression rVals = SINGLETON.getRecentRandom();
        long start = t.getCurrentThreadCpuTime();
        
        @SuppressWarnings("unused")
		ListExpression b_count_crypt_decrypt = SINGLETON.decrypt(b_count_crypt, rVals, STATICKEY.SINGLETON.PUBLIC_KEY);
        long end = t.getCurrentThreadCpuTime();
        
        System.err.println(end-start);
        
        /*
        File f = new File("out");
        FileOutputStream fo = new FileOutputStream(f);
        byte[] bytes = b_count_crypt.toVerbatim();
        fo.write(bytes);
        fo.close();
        */
    }
}
