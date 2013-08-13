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

import sexpression.ASExpression;

import java.math.BigInteger;
import java.util.Map;

/**
 * Interface for all Tallier implementations.
 * 
 * @see supervisor.model.tallier.EncryptedTallier
 * @see supervisor.model.tallier.Tallier
 * @author Montrose
 *
 */
public interface ITallier {
	
	/**
	 * Gets the report of the total tally
	 * 
	 * 
	 * @return the report as a map of Candidiate to votes received.
	 */
	public Map<String, BigInteger> getReport();
	
	/**
	 * Records the votes from the given ballot, as an S-Expression in byte array
	 * format
	 * 
	 * @param ballot - Verbatim version of the ballot to totall
	 * @param nonce - Nonce of this voting transaction
	 */
	public void recordVotes(byte[] ballot, ASExpression nonce);
	
	/**
	 * Called to indicate that the voting transactioned indicated by the nonce is complete, and should be counted
	 * in the final tally.
	 * 
	 * @param nonce - Nonce of this voting transaction
	 */
	public void confirmed(ASExpression nonce);
	
	/**
	 * Called to indicate that a voting transaction is being challenged.
	 * This should result in the destruction of the ballot in the tallier.
	 * 
	 * @param nonce - Nonce of this voting transaction
	 */
	public void challenged(ASExpression nonce);
}