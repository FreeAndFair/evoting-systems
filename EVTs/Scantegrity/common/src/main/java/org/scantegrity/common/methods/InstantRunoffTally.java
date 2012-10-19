package org.scantegrity.common.methods;
import java.util.TreeMap;
import java.util.Vector;
import java.util.logging.Level;

import org.scantegrity.common.Ballot;
import org.scantegrity.common.BallotStyle;
import org.scantegrity.common.Contest;
import org.scantegrity.common.Contestant;
import org.scantegrity.common.Logging;
import org.scantegrity.common.constants.TallyConstants;


/*
 * @(#)InstantRunoffTally.java
 *  
 * Copyright (C) 2009 Scantegrity Project
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
 * InstantRunoffTally accepts and publishes election results using Instant Runoff
 * rules. The current ruleset and reporting is specific to Takoma Park, who's 
 * relevant law I will cite here:
 * 
 * (c) An instant runoff voting system shall be used in order to elect the Mayor
 * and Councilmembers with a majority of votes by allowing voters to rank 
 * candidates in order of choice. Instructions on instant runoff voting 
 * provided to voters shall conform substantially to the following 
 * specifications, although subject to modification based on ballot design and 
 * voting system: “Vote for candidates by indicating your first-choice 
 * candidate, your second-choice candidate, and so on. Indicate your first 
 * choice by marking the number “1" beside a candidate’s name, your second 
 * choice by marking the number “2" beside that candidate’s name, your third 
 * choice by marking the number “3", and so on, for as many choices as you wish.
 * You are free to rank only one candidate, but ranking additional candidates 
 * cannot help defeat your first-choice candidate. Do not mark the same number 
 * beside more than one candidate. Do not skip numbers.”
 * (d) The first choice marked on each ballot shall be counted initially by the 
 * judges as one vote. If any candidate receives a majority of the first 
 * choices, that candidate shall be declared elected.
 * (e) If no candidate receives a majority of first choices, the judges of 
 * election shall conduct an instant runoff consisting of additional rounds of 
 * ballot counting. In every round of counting, each ballot is counted as one 
 * vote for that ballot’s highest ranked advancing candidate. “Advancing 
 * candidate” means a candidate for that office who has not been eliminated. A 
 * candidate receiving a majority of valid votes in a round shall be declared 
 * elected.
 * If no candidate receives a majority of valid votes in a round, the candidate 
 * with the fewest votes shall be eliminated, and all ballots shall be 
 * recounted. This process of eliminating the candidate with the fewest votes 
 * and recounting all ballots shall continue until one candidate receives a 
 * majority of the valid votes in a round. 
 * (f) To facilitate ballot counting in any round, the judges of election may 
 * eliminate all candidates with no mathematical chance of winning. A candidate 
 * has no mathematical chance of winning if the sum total of all votes credited 
 * to that candidate and all candidates with fewer votes is less than the number
 * of votes credited to the candidate with the next greatest number of votes.
 * (g) If a ballot has no more available choices ranked on it, that ballot 
 * shall be declared “exhausted” and not counted in that round or any 
 * subsequent round. Ballots skipping one number shall be counted for that 
 * voter’s next clearly indicated choice, but ballots skipping more than one 
 * number shall be declared exhausted when this skipping of numbers is reached. 
 * Ballots with two or more f the same number shall be declared exhaused when 
 * such duplicate rankings are reached unless only one of the candidates with 
 * the duplicate ranking is an advancing candidate.
 * (h) In the event of a tie that effects the outcome of the election, the 
 * tie shall be broken by comparing the votes of the tied candidates in the 
 * previous rounds of counting, starting with the count immediately preceding 
 * the round in which the tie occurs. If one of the tied candidates had more 
 * votes than the remaining tied candidates in the preceding round or an 
 * earlier round of counting, then that candidate shall advance and the others 
 * shall be eliminated. If the candidates were tied in each preceding round, 
 * then the tie shall be resolved by lot. In the event that this tie occurs 
 * between or among all remaining candidates, then a runoff election between or 
 * among the tied candidates shall be held within forty-five (45) days after 
 * the date of the election.
 * 
 * @author Richard Carback
 * @version 0.0.2 
 * @date 09/07/09
 */

public class InstantRunoffTally implements TallyMethod {	

	/* (non-Javadoc)
	 * @see org.scantegrity.lib.methods.TallyMethod#validateBallot(org.scantegrity.scanner.Contest, org.scantegrity.scanner.Ballot)
	 */
	public TreeMap<String, String> validateContest(int p_contestId,
													Ballot p_ballot)
	{
		if (!p_ballot.hasContest(p_contestId)) return null;
		TreeMap<String, String> l_res = new TreeMap<String, String>();
		//This models some of the iterator functionality, but since counting
		//and validation are different beasts, we can't really use it.
		//if ()
		Integer l_bData[][] = p_ballot.getContestData(p_contestId);
		if (l_bData.length == 0 || l_bData[0].length == 0) return null;
		
		for (int l_j = 0; l_j < l_bData[0].length; l_j++)
		{
			int l_rankCnt = 0;
			for (int l_i = 0; l_i < l_bData.length; l_i++)
			{
				if (l_bData[l_j][l_i] == 1) 
					l_rankCnt++;
				
				if(l_bData[l_j][l_i] == 1 && l_rankCnt > 1) l_res.put("Rank " + (l_i + 1), TallyConstants.OVERVOTE_ROW);
			}
		}
		
		for (int l_i = 0; l_i < l_bData[0].length; l_i++)
		{
			int l_rankCnt = 0;
			for (int l_j = 0; l_j < l_bData.length; l_j++)
			{
				if (l_bData[l_j][l_i] == 1) l_rankCnt++;
			}
			String l_rankName = "Rank " + (l_i+1); 
			if (l_rankCnt == 1)
			{
				if(!l_res.containsKey(l_rankName))
					l_res.put(l_rankName, TallyConstants.VOTE_RECORDED);
			}
			else if (l_rankCnt == 0) 
			{
				if(!l_res.containsKey(l_rankName))
					l_res.put(l_rankName, TallyConstants.NO_VOTE);
			}
			else l_res.put(l_rankName, TallyConstants.OVERVOTE);
		}
		
		return l_res;
	}	
	
	
	/* (non-Javadoc)
	 * @see org.scantegrity.lib.methods.TallyMethod#tally(int, java.util.Vector, java.util.Vector)
	 */
	public ContestResult tally(Contest p_contest, Vector<ContestChoice> p_ballots)
	{
		/** TODO: Should not need contestant information anymore. Formatting
		 * and normalization is assumed to be done outside this function.
		 */
		
		//ID for this contest - Used in reporting.
		int l_id = p_contest.getId();
		//Each candidate gets his own stack.
		TreeMap<Contestant, Vector<ContestChoiceIterator>> l_stacks;
		Vector<Contestant> l_contestants;
		//The ballots to count.
		Vector<ContestChoiceIterator> l_countMe;
		
		//Get all the ballots
		l_countMe = new Vector<ContestChoiceIterator>();
		for (ContestChoice l_ballot : p_ballots)
		{
			l_countMe.add(new ContestChoiceIterator(l_ballot));
		}
		
		//currently available stacks
		l_stacks = new TreeMap<Contestant, Vector<ContestChoiceIterator>>();
		l_contestants = p_contest.getContestants();
		l_contestants.add(new Contestant(-2, "Exhausted Pile"));
		for (Contestant l_c: p_contest.getContestants())
		{
			l_stacks.put(l_c, new Vector<ContestChoiceIterator>());	
		}
		
		//Results Objects
		IRVContestResult l_res = new IRVContestResult(l_id, l_contestants);		
		IRVContestResult.Round l_curRound = l_res.new Round(1);
		IRVContestResult.Round l_prevRound = null;
		
		
		//System.out.println("Started with: " + p_ballots.size());

		//Stack's for resolving ties.
		Vector<TreeMap<Contestant, Vector<ContestChoiceIterator>>> l_tieStack;
		l_tieStack = new Vector<TreeMap<Contestant, Vector<ContestChoiceIterator>>>();
		Vector<IRVContestResult.Round> l_roundStack;
		l_roundStack = new Vector<IRVContestResult.Round>();
		Vector<Contestant> l_canStack = new Vector<Contestant>();		
		
		//Process each round, create a round result for each iteration.
		int l_numBallots = l_countMe.size();
		TreeMap<Integer, Vector<Contestant>> l_curRank;
		do
		{
			doRound(l_stacks, l_countMe);
			
			//Record current totals
			Vector<ContestChoiceIterator> l_curStack;
			for (int l_i = 0; l_i < l_contestants.size(); l_i++)
			{
				//Pull stack for this contestant
				l_curStack = l_stacks.get(l_contestants.elementAt(l_i));
				int l_totals = 0;
				if (l_curStack != null) l_totals = l_curStack.size();
				int l_delta = l_totals;

				if (l_prevRound != null)
				{
					l_delta = l_totals - l_prevRound.c_totals.get(l_i);
				}

				l_curRound.c_totals.set(l_i, l_totals);
				l_curRound.c_delta.set(l_i, l_delta);
			}

			l_curRank = getRankOrder(l_stacks);			
			/**
			 * NOTE: Ties are OK, as long as they aren't on the bottom AND
			 * the bottom candidates are still mathematically viable.
			 */
			Vector<Contestant> l_defeated = getDefeated(l_curRank, l_stacks);
			
			if (l_defeated == null || l_defeated.size() == 0)
			{
				//A Tie!
				Vector<Contestant> l_tied = l_curRank.get(l_curRank.lastKey());
				String l_tieNote = "Candidates Tied: ";
				for (Contestant l_c : l_tied) {
					l_tieNote += l_c.toString() + ", ";
				}
				l_curRound.addNote(l_tieNote);
				
				//Try to break the tie
				Contestant l_tieCan;
				l_tieCan = breakTie(l_tied, l_curRound, l_res.c_rounds);
				if (l_tieCan == null)
				{
					//Tie could not be broken, is this the last possible round?
					if (l_stacks.size() == 3)
					{
						l_curRound.addNote("Tie between last 2 candidates " 
											+ "cannot be broken. No Winner!");
						
					}
					else
					{
						/**
						 * We now save the "state" which get's popped when a winner
						 * is detected. Pick one state, push the other possibilities
						 * onto the stack, then continue this chain.
						 */
						l_curRound.addNote("Tie is Unbreakable, computing all"
											+ " possibilities...");
						int l_i;
						for (l_i = 0; l_i < l_tied.size()-1; l_i++)
						{
							//System.out.println("Adding alternate exec: " + l_i);
							TreeMap<Contestant, Vector<ContestChoiceIterator>> l_tmpStack;
							IRVContestResult.Round l_tmpRnd;
							Contestant l_tmpCan; 
							l_tmpStack = copyStack(l_stacks);
							l_tmpRnd = l_curRound.clone();
							l_tmpCan = l_tied.get(l_i);
							
							l_tmpRnd.c_desc += ", Dropped " + l_tmpCan.toString()
												+ " in Round " + l_curRound.c_id;
							l_tmpRnd.addNote(l_tmpCan.getName() 
												+ " DEFEATED (TIE)");
							l_tmpRnd.c_state.set(l_contestants.indexOf(l_tmpCan), 
									"DEFEATED (TIE), Round " + l_curRound.getId());
							
							l_canStack.add(l_tmpCan);
							l_roundStack.add(l_tmpRnd);
							l_tieStack.add(l_tmpStack);
						}
						
						//Chosen state is always 0
						l_curRound.c_desc += ", Dropped " + l_tied.get(l_i).toString()
											+ " in Round " + l_curRound.c_id;
						l_curRound.addNote(l_tied.get(l_i).getName() 
											+ " DEFEATED (TIE)");
						l_curRound.c_state.set(l_contestants.indexOf(l_tied.get(l_i)), 
									"DEFEATED (TIE), Round " + l_curRound.getId());
						l_countMe = new Vector<ContestChoiceIterator>();
						l_countMe.addAll(l_stacks.get(l_tied.get(l_i)));
						l_stacks.remove(l_tied.get(l_i));
					}
					l_defeated = null;
				}
				else
				{
					l_defeated = new Vector<Contestant>();
					l_curRound.addNote(l_tieCan.toString() 
									+ " had fewer votes than " 
									+ "other candidates in a previous round.");
					l_defeated.add(l_tieCan);
				}	
			}
			
			if (l_defeated != null)
			{
				l_countMe = new Vector<ContestChoiceIterator>();
				for (Contestant l_c : l_defeated) 
				{
					l_countMe.addAll(l_stacks.get(l_c));
					l_stacks.remove(l_c);
					l_curRound.addNote(l_c.getName() + " DEFEATED");
					l_curRound.c_state.set(l_contestants.indexOf(l_c), 
									"DEFEATED, Round " + l_curRound.getId());
					//System.out.println(l_c.getName() + " DEFEATED");
				}
			}

			//Detect a winner
			//Is there a winner with 50%+1 vote majority? End now.
			Vector<Contestant> l_top = l_curRank.get(l_curRank.firstKey());
			if (l_top.size() == 1 
					&& l_numBallots/l_stacks.get(l_top.get(0)).size() < 2.0)
			{
				l_curRound.addNote("END, Majority winner is " + l_top.get(0));
				l_curRound.c_state.set(l_contestants.indexOf(l_top.get(0)), 
										"WINNER, Round " + l_curRound.getId());
				//Need something here to end counting.. but not a big problem..
			}
			else if (l_stacks.size() <= 2)
			{
				//Nothing left to count
				l_curRound.addNote("END, winner is " + l_stacks.lastKey());
				l_curRound.c_state.set(l_contestants.indexOf(l_stacks.lastKey()), 
										"WINNER, Round " + l_curRound.getId());
			}
			
			//Save round and report results
			l_res.addRound(l_curRound);
			//System.out.println(l_curRound.toString());						
			
			//Continue execution if there are remaining ties that need to 
			//be computed.
			if ((l_stacks.size() <= 2 && l_tieStack.size() > 0) 
					|| (l_stacks.size() == 3 && l_tieStack.size() > 0 
							&& l_curRank.size() == 1 
							&& l_curRank.get(0).size() == 2))
			{
				int l_index = l_tieStack.size()-1;
				l_stacks = l_tieStack.get(l_index);
				l_curRound = l_roundStack.get(l_index);
				Contestant l_dropCan = l_canStack.get(l_index);
				l_countMe = new Vector<ContestChoiceIterator>();
				l_countMe.addAll(l_stacks.get(l_dropCan));
				l_stacks.remove(l_dropCan);
				l_tieStack.remove(l_index);
				l_roundStack.remove(l_index);
				l_canStack.remove(l_index);
			}

			//System.out.println("Alt Size: " + l_tieStack.size());
			//System.out.println("Stack Size: " + l_stacks.size());
			//Set up next round.
			l_prevRound = l_curRound;
			l_curRound = l_res.new Round(l_prevRound);
		} while ((l_stacks.size() > 2 //End, or tied ending
					|| l_tieStack.size() > 0) && l_res.getRounds().size() < 100); 
		
		l_res.setRanking(l_curRank);
		
		return l_res;
	}

	/**
	 * @param p_stacks The current stacks
	 * @param p_ballots The current countable stack
	 * @param p_defeatedIds the defeated candidate IDs.
	 */
	private void doRound(TreeMap<Contestant, Vector<ContestChoiceIterator>> p_stacks,
						Vector<ContestChoiceIterator> p_ballots)
	{
		/** TODO: The way we get valid contestants is hack-ish. Make it cleaner.
		 */
		for (ContestChoiceIterator l_ballot : p_ballots)
		{
			Vector<Integer> l_cans = new Vector<Integer>();
			for (Contestant l_c : p_stacks.keySet()) l_cans.add(l_c.getId());
			Vector<Integer> l_nextIDs = l_ballot.getNext(l_cans);
			//System.out.println(l_nextIDs.toString());
			Contestant l_contestant = null;
			int l_cid = -1;
			if (l_nextIDs!= null && l_nextIDs.size() == 1)
			{
				l_cid = l_nextIDs.get(0);
			}
			else
			{
				//Could be overvote, could be exhaust, result is the same.
				l_cid = -2;
			}
			
			for (Contestant l_c : p_stacks.keySet())
			{
				if (l_c.getId() == l_cid) 
				{
					l_contestant = l_c;
				}
			}
			
			if (l_contestant == null) l_contestant = p_stacks.firstKey();
			
			//System.out.println("Adding " + l_cid
			//		+ " to " + l_contestant.toString());
			Vector<ContestChoiceIterator> l_b = p_stacks.get(l_contestant);
			l_b.add(l_ballot);
			//l_stacks.get(l_contestant).add(l_ballot);	
		}
	}
	
	
	private TreeMap<Integer, Vector<Contestant>> getRankOrder(
							TreeMap<Contestant, Vector<ContestChoiceIterator>> p_stacks)
	{
		Object l_keys[] = p_stacks.keySet().toArray();
		TreeMap<Integer, Vector<Contestant>> l_tmp, l_final;
		l_tmp = new TreeMap<Integer, Vector<Contestant>>();		
		l_final = new TreeMap<Integer, Vector<Contestant>>();
		
		//Each key becomes the target, the new keys are the size, order is
		//automagically computed via treemap.
		for (Object l_k: l_keys) 
		{
			Contestant l_key = (Contestant)l_k;
			if (l_key.getId() == -2) continue; //Skip the exhausted pile
			//System.out.print(l_key.toString() + ":");
			//System.out.println(", Size: " + p_stacks.get(l_key).size());
			if (!l_tmp.containsKey(p_stacks.get(l_key).size()))
			{
				l_tmp.put(p_stacks.get(l_key).size(), new Vector<Contestant>());
			}
			l_tmp.get(p_stacks.get(l_key).size()).add(l_key);
		}
		
		//Change each key to equivalent rank.
		l_keys = l_tmp.keySet().toArray();
		for (int l_i = 0; l_i < l_keys.length; l_i++)
		{
			l_final.put(l_i, l_tmp.get(l_tmp.lastKey()));
			l_tmp.remove(l_tmp.lastKey());
		}
		
		return l_final;
	}
	
	/**
	 * getDefeated 
	 * 	Determines the defeated candidate(s) based on their rank.  
	 * 
	 * @param p_rank Candidate rankings for the current round.
	 * @param p_stacks The stacks of ballots for the current round.
	 * @return the list of defeated candidates.
	 */
	private Vector<Contestant> getDefeated(
			TreeMap<Integer, Vector<Contestant>> p_rank, 
			TreeMap<Contestant, Vector<ContestChoiceIterator>> p_stacks)
	{
		/** TODO: Try to break a tie, and report the loser, if possible. */
		Vector<Contestant> l_defeated = new Vector<Contestant>();
		Vector<Contestant> l_lowCans;
		Integer l_curKey = p_rank.lastKey();
		if (l_curKey == null || p_rank.lowerKey(l_curKey) == null)
		{
			return l_defeated;
		}
		l_lowCans = p_rank.get(l_curKey);
		l_defeated.addAll(l_lowCans);
		
		/* This code would normally total all the defeated candidates.
		 * We only want the lowest candidate. If there is a tie for lowest, 
		 * then we will return more than one candidate.
		l_upCan = p_rank.get(p_rank.lowerKey(l_curKey));
		//Only need 1 upcan
		l_upCan.setSize(1);
		Integer l_lowTot, l_upTot;
		l_lowTot = getContestantTotals(l_lowCans, p_stacks);
		l_upTot = getContestantTotals(l_upCan, p_stacks);
		//System.out.println(l_lowTot + ", " + l_upTot);
 
		while (l_lowTot < l_upTot)
		{
			l_defeated.addAll(l_lowCans);
			
			l_curKey = p_rank.lowerKey(l_curKey);
			if (l_curKey == null || p_rank.lowerKey(l_curKey) == null) break;
			l_lowCans = p_rank.get(l_curKey);
			l_upCan = p_rank.get(p_rank.lowerKey(l_curKey));
			//Only need 1 upcan
			l_upCan.setSize(1);

			l_lowTot += getContestantTotals(l_lowCans, p_stacks);
			l_upTot = getContestantTotals(l_upCan, p_stacks);
		}*/
		
		return l_defeated;
	}
	
	/**
	 * Travels up the results tree matching the current execution context. 
	 * Looks to see if at one point one of the candidates had fewer votes than 
	 * all the others during that round. If true, the ranks are ordered and 
	 * returned, if not, null is returned to signify an unbreakable tie.
	 * 
	 * This method assumes a single chain of execution, do not send multiple 
	 * chains to it or it will freak out.
	 * 
	 * @param p_tied
	 * @param p_rounds
	 * @return
	 */
	private Contestant breakTie(Vector<Contestant> p_tied,
								IRVContestResult.Round p_curRound,
								Vector<IRVContestResult.Round> p_rounds)
	{
		//Sanity check
		if (p_tied.size() <= 1)	return null;
		
		//Tree Travel!
		Contestant l_lowest, l_nextLowest;
		for (int l_i = p_rounds.size()-1; l_i >= 0; l_i--)
		{
			IRVContestResult.Round l_tieRound = p_rounds.get(l_i);
			if (p_curRound.getDesc().startsWith(l_tieRound.getDesc())
					&& p_curRound.getId() > l_tieRound.getId())
			{				
				Vector<Integer> l_curTotals = l_tieRound.getTotals(); 
				//Compare each candidate, see if there is a lowest.
				l_lowest = p_tied.firstElement();
				l_nextLowest = p_tied.get(1); 
				int l_lowSize = l_curTotals.get(l_lowest.getId());
				for (int l_j = 1; l_j < p_tied.size(); l_j++)
				{
					if (l_lowSize > l_curTotals.get(p_tied.get(l_j).getId()))
					{
						l_nextLowest = l_lowest;
						l_lowest = p_tied.get(l_j);
						l_lowSize = l_curTotals.get(p_tied.get(l_j).getId());
					}
				}
				//Did we actually find a lowest Candidate?
				if (l_curTotals.get(l_lowest.getId()) 
						< l_curTotals.get(l_nextLowest.getId()))
				{
					return l_lowest;
				}
				//Else try again.
			}	
		}
		
		return null;
	}
	
	/**
	 * Make a deep copy of the current ballot stack.
	 * 
	 * @param l_stack the current ballot stack.
	 * @return A copy of the given stack.
	 */
	private TreeMap<Contestant, Vector<ContestChoiceIterator>> copyStack(
					TreeMap<Contestant, Vector<ContestChoiceIterator>> l_stack)
	{
		TreeMap<Contestant, Vector<ContestChoiceIterator>> l_new;
		l_new = new TreeMap<Contestant, Vector<ContestChoiceIterator>>();
		Contestant l_c = l_stack.firstKey();
		do
		{
			Vector<ContestChoiceIterator> l_bi;
			l_bi = new Vector<ContestChoiceIterator>();
			for (ContestChoiceIterator l_b : l_stack.get(l_c))
			{
				l_bi.add(new ContestChoiceIterator(l_b));
			}
			l_new.put(l_c, l_bi);
			
		} while ((l_c = l_stack.higherKey(l_c)) != null);
		
		return l_new;
	}


	/**
	 * This method checks the given contest data to verify that there 
	 * are no voting errors that will require human verification of the 
	 * votes in the ERM. If there are errors (Overvotes 
	 * or Undervotes) then we will have to save the ballot image have 
	 * the election judge manually process the ballot in the ERM like we do 
	 * with Write-Ins. 
	 * 
	 * @param Integer[][] p_contest_data: The contest data in 2d array of contestant id and 
	 * actual ballot marks. 
	 * @param Vector<String> p_error_condition: String error condition where we will save the 
	 * error condition we find if any. 
	 * 
	 * @return boolean: If an error condition is found. 
	 */
	public boolean hasVotingErrors(Integer[][] p_contest_data,
			Vector<String> p_error_conditions, Logging p_log) {
		boolean l_undervote = false; 
		boolean l_overvote = false;
		int l_num_columns = p_contest_data[0].length;
		int[] l_zero_count = new int[l_num_columns]; 
		int[] l_one_count = new int[l_num_columns];
		
		//go through each contest
		for (Integer[] l_contestant: p_contest_data) { 
			//p_log.log(Level.INFO, "Contestant: " + l_contestant.toString()); //TODO: testing
			//go through each mark for each contestant row 
			//and mark how many marks are marked and not marked
			for (int i = 0; i < l_contestant.length; i++) {
				int l_mark = l_contestant[i]; 
				if (l_mark == 0) {
					//p_log.log(Level.INFO, "Zero count incremented: " + l_mark); //TODO: testing
					l_zero_count[i]++; 
				} else {
					//p_log.log(Level.INFO, "One count incremented: " + l_mark); //TODO: testing
					l_one_count[i]++; 
				}
			}
		}
		
		//if we have all zeroes in the column then we have an undervote
		for (int l_column = 0; l_column < l_num_columns; l_column++ ) {
			// Limit this to only checking column (rank) 1. 
			if (l_column == 0 && l_zero_count[l_column] == p_contest_data.length) {
				l_undervote = true;
				//p_log.log(Level.INFO, "Undervote Found in column: " + l_column); //TODO: testing
				p_error_conditions.add("Undervote in Choice " + (l_column + 1));
			}
			
			//if we have more than 1 mark in the column we have an overvote
			if (l_one_count[l_column] > 1) {
				l_overvote = true;
				//p_log.log(Level.INFO, "Overvote Found in column: " + l_column); //TODO: testing
				p_error_conditions.add("Overvote in Choice " + (l_column + 1));
			}
		}
		
		if (l_overvote) { 
			return l_overvote; 
		}
		
		if (l_undervote) {
			return l_undervote;
		}
		
		return false; 
	}

}