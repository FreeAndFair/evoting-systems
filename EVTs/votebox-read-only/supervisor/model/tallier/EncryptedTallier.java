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

package supervisor.model.tallier;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;

import auditorium.Bugout;
import auditorium.Key;

import sexpression.*;

import sexpression.ASExpression;
import sexpression.stream.ASEInputStreamReader;
//import sexpression.stream.Base64;
import sexpression.stream.InvalidVerbatimStreamException;
import votebox.crypto.ElGamalCrypto;
import votebox.crypto.Pair;

public class EncryptedTallier implements ITallier {
	private static ASExpression PATTERN = new ListWildcard(new ListExpression(StringWildcard.SINGLETON, Wildcard.SINGLETON));
	
	private Key _privateKey = null;
	
	private Map<String, Pair<BigInteger>> _votes = new HashMap<String, Pair<BigInteger>>();
	
	public EncryptedTallier(Key privateKey){
		_privateKey = privateKey;
	}
	
	/**
	 * @param privateKey - the appropriate ElGamal private key
	 * @return a text description of the outcome of the election.
	 */
	public Map<String, BigInteger> getReport() {
		
		Map<String, BigInteger> results = new HashMap<String, BigInteger>();
		
		for(String candidate : _votes.keySet()){
			Pair<BigInteger> value = _votes.get(candidate);
			
			results.put(candidate, ElGamalCrypto.SINGLETON.decrypt(_privateKey, value));
		}//for
		
		return results;
	}

	public void recordVotes(byte[] ballotBytes, ASExpression ignoredNonce) {
		ASEInputStreamReader in = new ASEInputStreamReader(
				new ByteArrayInputStream(ballotBytes));
		try {
			ASExpression sexp = in.read();
			//Check that the ballot is well-formed
			if(PATTERN.match(sexp) != NoMatch.SINGLETON){
				ListExpression ballot = (ListExpression)sexp;
				
				for(ASExpression voteE : ballot){
					ListExpression vote = (ListExpression)voteE;
					String key = vote.get(0).toString();
					ListExpression encryptedVote = (ListExpression)vote.get(1);
					String pairPart1 = encryptedVote.get(0).toString();
					String pairPart2 = encryptedVote.get(1).toString();
					
					Pair<BigInteger> pair = new Pair<BigInteger>(new BigInteger(pairPart1), new BigInteger(pairPart2));
					
					Pair<BigInteger> currentTotal = _votes.get(key);
					
					if(currentTotal != null){
						//We generate a new cyphertext which has a plain text equivalent to
						// D(pair) + D(currentTotal) - the sum of the decrypted pair and currentTotal values -
						// by multiplying pair and currentTotal.
						currentTotal = ElGamalCrypto.SINGLETON.mult(pair, currentTotal);
					}else{
						currentTotal = pair;
					}//if
					
					_votes.put(key, currentTotal);
				}//for
			}else{
				Bugout.err("Received a malformed ballot.\n"+sexp+" does not match "+PATTERN);
			}//if
		}catch(IOException e){
		    Bugout.err("Encounted IOException when counting encrypted vote: "+e.getMessage());
		} catch (InvalidVerbatimStreamException e) {
			Bugout.err("Encounted InvalidVerbatimStream when counting encrypted vote: "+e.getMessage());
		}
	}

	public void challenged(ASExpression nonce) {
		throw new RuntimeException("EncryptedTallier.challenged NOT IMPLEMENTED");
	}

	public void confirmed(ASExpression nonce) {
		throw new RuntimeException("EncryptedTallier.confirmed NOT IMPLEMENTED");
	}

}
