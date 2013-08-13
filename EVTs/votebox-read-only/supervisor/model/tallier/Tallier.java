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
import java.util.TreeMap;

import sexpression.*;
import sexpression.stream.*;

/**
 * Temporary class for tallying votes as they are seen (unencrypted) on the
 * network
 * 
 * @author cshaw
 */
public class Tallier implements ITallier{

	private static ASExpression pattern = new ListWildcard(new ListExpression(
			StringWildcard.SINGLETON, new ListWildcard(Wildcard.SINGLETON)));

	private TreeMap<String, HashMap<String, Integer>> votes;

	/**
	 * Constructs a new Tallier with its counts zeroed out
	 */
	public Tallier() {
		votes = new TreeMap<String, HashMap<String, Integer>>();
	}

	/**
	 * @see supervisor.model.tallier.ITallier#getReport()
	 */
	public Map<String, BigInteger> getReport() {
		Map<String, BigInteger> results = new HashMap<String, BigInteger>();
		
		for(Map<String, Integer> race : votes.values()){
			for(String candidate : race.keySet())
				results.put(candidate, new BigInteger(""+race.get(candidate)));
		}//for
		
		return results;
		
		/*String res = "";
		for (String racename : votes.keySet()) {
			res += racename + ":\n";
			HashMap<String, Integer> race = votes.get(racename);
			for (String candidate : race.keySet()) {
				int numvotes = race.get(candidate);
				res += "  " + candidate + " -- " + numvotes;
				if (numvotes > 1)
					res += " votes\n";
				else
					res += " vote\n";
			}
			res += "\n";
		}
		res += "Candidates receiving 0 votes are not shown";
		return res;*/
	}

	/**
	 * @see supervisor.model.tallier.ITallier#recordVotes(byte[])
	 */
	public void recordVotes(byte[] ballot, ASExpression ignoredNonce) {
		ASEInputStreamReader in = new ASEInputStreamReader(
				new ByteArrayInputStream(ballot));
		try {
			ASExpression sexp = in.read();
			if (pattern.match(sexp) != NoMatch.SINGLETON) {
				ListExpression list = (ListExpression) sexp;
				for (ASExpression s : list.getArray()) {
					ListExpression vote = (ListExpression) s;
					String race = vote.get(0).toString();
					ListExpression choiceExp = (ListExpression) vote.get(1);
					if (choiceExp.size() > 0) {
						String choice = choiceExp.get(0).toString();
						HashMap<String, Integer> raceVals = votes.get(race);
						if (raceVals == null) {
							raceVals = new HashMap<String, Integer>();
							votes.put(race, raceVals);
						}
						Integer val = raceVals.get(choice);
						if (val == null) {
							votes.get(race).put(choice, 1);
						} else {
							votes.get(race).put(choice, val + 1);
						}
					}
				}
			}
		} catch (IOException e) {
			e.printStackTrace();
		} catch (InvalidVerbatimStreamException e) {
			System.err.println("Tallier.recordVotes(): error: ballot wasn't correctly formatted, so couldn't do the tally");
			System.err.println("Ballot data: " + ballot);
			System.err.println("exception: " + e);
		}
	}

	public void challenged(ASExpression nonce) {
		throw new RuntimeException("Tallier.challenged NOT IMPLEMENTED");
	}

	public void confirmed(ASExpression nonce) {
		throw new RuntimeException("Tallier.confirmed NOT IMPLEMENTED");
	}
}
