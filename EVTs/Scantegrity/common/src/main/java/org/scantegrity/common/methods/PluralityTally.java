/*
 * @(#)PluralityTally.java
 *  
 * Copyright (C) 2008-2009 Scantegrity Project
 * 
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */

/**
 * PluralityTally accepts and publishes election results using the first past the
 * post or plurality election method.
 * 
 * This is currently a quickly written example. Don't take this to be any sort 
 * of best practice implementation.
 * 
 * @author Richard Carback
 * @version 0.0.1 
 * @date 01/03/09
 */
package org.scantegrity.common.methods;

import java.util.Map;
import java.util.TreeMap;
import java.util.Vector;

import org.scantegrity.common.Ballot;
import org.scantegrity.common.BallotStyle;
import org.scantegrity.common.Contest;
import org.scantegrity.common.Contestant;
import org.scantegrity.common.Logging;
import org.scantegrity.common.constants.TallyConstants;

public class PluralityTally implements TallyMethod {
	
	/**
	 * Constructor - plurality has no options that need to be 
	 * set.
	 * 
	 * @param p_names
	 */
	public PluralityTally() {
	}

	/* (non-Javadoc)
	 * @see org.scantegrity.lib.methods.TallyMethod#validateContest(int, org.scantegrity.scanner.Ballot)
	 */
	public TreeMap<String, String> validateContest(int p_contestId,
			Ballot p_ballot)
	{
		TreeMap<String, String> l_res = new TreeMap<String, String>();
		
		int l_sum = 0;
		Integer l_bData[][] = p_ballot.getContestData(p_contestId);
		if (l_bData.length == 0 || l_bData[0].length == 0) return null;
		for (int l_i = 0; l_i < l_bData.length; l_i++)
		{
			if (l_bData[l_i][0] == 1) l_sum++;
		}
		if (l_sum == 0) l_res.put("", TallyConstants.NO_VOTE);
		else if (l_sum == 1) l_res.put("", TallyConstants.VOTE_RECORDED);
		else l_res.put("", TallyConstants.OVERVOTE);
		return l_res;
	}
	
	
	/* (non-Javadoc)
	 * @see org.scantegrity.lib.methods.TallyMethod#tally(org.scantegrity.scanner.Contest, java.util.Vector)
	 */
	public ContestResult tally(Contest p_contest, Vector<ContestChoice> p_ballots)
	{
		PluralityContestResult l_res = new PluralityContestResult();
		TreeMap<Contestant, Vector<ContestChoice>> l_stacks;
		Vector<Contestant> l_contestants;		
		l_contestants = new Vector<Contestant>(p_contest.getContestants());
		l_contestants.add(new Contestant(-2, "Invalid Ballots"));
		
		l_stacks = new TreeMap<Contestant, Vector<ContestChoice>>();
		Vector<Integer> l_conIds = new Vector<Integer>();
		for (Contestant l_c: l_contestants)
		{
			l_stacks.put(l_c, new Vector<ContestChoice>());	
			l_conIds.add(l_c.getId());
		}

		for (ContestChoice l_b : p_ballots)
		{
			int l_bData[][] = l_b.getChoices();
			int l_c = -1;
			for (int l_i = 0; l_i < l_bData.length; l_i++)
			{
				if (l_bData[l_i][0] == 1)
				{
					if (l_c == -1)
					{ 
						//Record Vote
						l_c = l_i;
					}
					else 
					{
						//OverVote
						l_c = -2;
						break;
					}
				}
			}
			//No Vote
			if (l_c == -1) l_c = -2;
			
			l_stacks.get(l_contestants.get(l_conIds.indexOf(l_c))).add(l_b);
		}

		TreeMap<Integer, Vector<Contestant>> l_rank = getRankOrder(l_stacks);
		Vector<Integer> l_totals = new Vector<Integer>();
		Integer l_key = l_rank.firstKey();
		while (l_key != null)
		{
			l_totals.add(l_stacks.get(l_rank.get(l_key).get(0)).size());
			l_key = l_rank.higherKey(l_key);
		}
		
		l_res.setRanking(l_rank);
		l_res.setTotals(l_totals);
		
		return l_res;
	}

	
	/**
	 * This is a c/p from the Runoff with 2 minor changes.. probably should 
	 * join this together or make it "better", not sure how.
	 * 
	 * @param p_stacks
	 * @return
	 */
	private TreeMap<Integer, Vector<Contestant>> getRankOrder(
			TreeMap<Contestant, Vector<ContestChoice>> p_stacks)
	{
		Object l_keys[] = p_stacks.keySet().toArray();
		TreeMap<Integer, Vector<Contestant>> l_tmp, l_final;
		l_tmp = new TreeMap<Integer, Vector<Contestant>>();
		l_final = new TreeMap<Integer, Vector<Contestant>>();

		// Each key becomes the target, the new keys are the size, order is
		// automagically computed via treemap.
		for (Object l_k : l_keys)
		{
			Contestant l_key = (Contestant) l_k;
			if (l_key.getId() == -2)
				continue; // Skip the exhausted pile
				// System.out.print(l_key.toString() + ":");
				// System.out.println(", Size: " + p_stacks.get(l_key).size());
			if (!l_tmp.containsKey(p_stacks.get(l_key).size()))
			{
				l_tmp.put(p_stacks.get(l_key).size(), new Vector<Contestant>());
			}
			l_tmp.get(p_stacks.get(l_key).size()).add(l_key);
		}

		// Change each key to equivalent rank.
		l_keys = l_tmp.keySet().toArray();
		for (int l_i = 0; l_i < l_keys.length; l_i++)
		{
			l_final.put(l_i, l_tmp.get(l_tmp.lastKey()));
			l_tmp.remove(l_tmp.lastKey());
		}

		return l_final;
	}

	@Override
	public boolean hasVotingErrors(Integer[][] p_contest_data, Vector<String> p_error_conditions, Logging c_log) {
		// TODO Auto-generated method stub
		return false;
	}
	
}