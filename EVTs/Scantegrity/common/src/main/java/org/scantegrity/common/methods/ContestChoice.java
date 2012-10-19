/*
 * @(#)ContestChoice.java
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
package org.scantegrity.common.methods;

import java.awt.image.BufferedImage;
import java.util.Arrays;
import java.util.Map;
import java.util.TreeMap;
import java.util.Vector;

import org.scantegrity.common.Ballot;
import org.scantegrity.common.BallotStyle;
import org.scantegrity.common.Contest;

/**
 * ContestChoice represents choices from one contest on one ballot for 
 * results publishing purposes. 
 * 
 * The ID 
 * 
 * @author Richard Carback
 *
 */

public class ContestChoice {
	
	public static final int INVALID = -1;
	/* Switches and defaults 
	public static final short O_ALLOWDUP = 1; /* default is no duplicates 
	public static final short O_SKIPONE = 2; /* default is skip none 
	public static final short O_SKIPALL = 4; /* default is skip none */
	
	//ContestChoice ID number. Does not correspond to a ballot ID, and 
	//is present to identify tally method problems.
	private int c_id = -1;
	//The contest id that this choice object refers to.
	private int c_contest = -1;
	//The contest choices. This is not raw 2d Ballot matrix data.
	//         v - The Rank
	private int[][] c_choices = null;
	//            ^ - The candidate ID

	private Integer c_ballotId = 0;
	private int c_ward = 0; 
	
	
	/**
	 * Create a blank contest choice object.
	 */
	public ContestChoice()
	{
		setId(-1);
		c_contest = -1;
		c_choices = null;
	}
	
	/**
	 * Create a ContestChoice Object using the given values.
	 * 
	 * @param p_id - a random identifier
	 * @param p_contestId - contest id number
	 * @param c_choices - the choice data for this contest.
	 */
	public ContestChoice(int p_id, int p_contestId, int[][] p_choices)
	{
		setId(p_id);
		c_contest = p_contestId;
				
		c_choices = new int[p_choices.length][];
		for (int l_i = 0; l_i < p_choices.length; l_i++)
		{
			c_choices[l_i] = new int[p_choices[l_i].length];
			System.arraycopy(p_choices, 0, c_choices, 0, p_choices[l_i].length);
		}
	}

	/**
	 * Copy Constructor
	 * 
	 * @param p_choice
	 */
	public ContestChoice(ContestChoice p_choice)
	{
		c_contest = p_choice.c_contest;
		c_id = p_choice.c_id;
		c_choices = new int[p_choice.c_choices.length][];
		for (int l_i = 0; l_i < p_choice.c_choices.length; l_i++)
		{
			c_choices[l_i] = new int[p_choice.c_choices[l_i].length];
			System.arraycopy(p_choice.c_choices[l_i], 0, c_choices[l_i], 0, 
								p_choice.c_choices[l_i].length);
		}
		c_ballotId = p_choice.c_ballotId; 
		c_ward = p_choice.c_ward; 
	}
	
	
	/**
	 * Using a ballot object, create a contest choice object.
	 * 
	 * @param p_id - a random identifier
	 * @param p_ballot - ballot object with raw data. 
	 * @param p_style - style object which has write-in and contestant mapping
	 * @param p_contest - for the contest id
	 */
	public ContestChoice(int p_id, Ballot p_ballot, BallotStyle p_style, 
							Contest p_contest)
	{
		setId(p_id);
		c_contest = p_contest.getId();
		
		c_choices = getChoices(p_ballot.getBallotData().get(c_contest));
		
		//Search and replace for different ballot styles
		normalizeChoiceStyle(p_style);
		
		//Search and replace for Write-Ins.
		//normalizeChoiceWriteIn(p_style, p_ballot);
		c_ballotId = p_ballot.getId();
		
		c_ward = Integer.parseInt(Character.toString(c_ballotId.toString().charAt(0)));
	}

	/**
	 * @param id the id to set
	 */
	public void setId(int id) {
		c_id = id;
	}

	/**
	 * @return the id
	 */
	public int getId() {
		return c_id;
	}

	public int getContest() {
		return c_contest;
	}

	public void setContest(int p_contest) {
		c_contest = p_contest;
	}
	
	public Integer getWard() { 
		return c_ward; 
	}
	
	public void setWard(Integer p_ward) { 
		c_ward = p_ward; 
	}

	public int[][] getChoices() {
		return c_choices;
	}

	public void setChoices(int[][] p_choices) {
		c_choices = p_choices;
	}

	public void setChoices(Integer[][] p_choices) {
		c_choices = getChoices(p_choices);
	}
	
	public Integer getBallotId() { 
		return c_ballotId; 
	}
	
	public void setBallotId(Integer p_ballotId) {
		c_ballotId = p_ballotId; 
	}
	
	private int[][] getChoices(Integer[][] p_raw)
	{
		//Gather ballot data into proper format.
		int[][] l_choices = new int[p_raw[0].length][];
		for (int l_i = 0; l_i < p_raw[0].length; l_i++)
		{
			Vector<Integer> l_tmpIds = new Vector<Integer>();
			for (int l_j = 0; l_j < p_raw.length; l_j++)
			{
				//System.out.println(l_j + ", " + l_i);
				if (p_raw[l_j][l_i] == 1)
				{
					l_tmpIds.add(l_j);
				}
			}
			
			if (l_tmpIds.size() == 0)
			{
				l_choices[l_i] = new int[1];
				l_choices[l_i][0] = INVALID;
			}
			else
			{
				l_choices[l_i] = new int[l_tmpIds.size()];
				for (int l_j = 0; l_j < l_choices[l_i].length; l_j++)
				{
					l_choices[l_i][l_j] = l_tmpIds.get(l_j);
				}
			}
		}
		return l_choices;
	}
	
	private void normalizeChoiceStyle(BallotStyle p_style)
	{
		if (!p_style.isValid()) return;
		
		int l_contestIndex;
		Vector<Integer> l_contestantMap;
		
		l_contestIndex = p_style.getContests().indexOf(new Integer(c_contest));
		l_contestantMap = p_style.getContestantIds().get(l_contestIndex);
		if( l_contestantMap == null || l_contestantMap.size() == 0 )
			return;
		
		//For each rank
		for (int l_i = 0; l_i < c_choices.length; l_i++)
		{
			//Replace each contestant
			for (int l_j = 0; l_j < c_choices[l_i].length; l_j++)
			{
					if( c_choices[l_i][l_j] >= 0 )
						c_choices[l_i][l_j] = l_contestantMap.get(c_choices[l_i][l_j]);
			}
		}	
	}
	
	private void normalizeChoiceWriteIn(BallotStyle p_style, Ballot p_ballot)
	{
		if (!p_style.isValid()) return;
		
		int l_contestIndex;
		/* TODO: The mapping should be provided to the contestchoice class, AFTER the 
		 * resolution manager has decided what it is.
		 * 
		 * TreeMap<Integer, BufferedImage> l_writeInMap;
		
		l_contestIndex = p_style.getContests().indexOf(new Integer(c_contest));
		l_writeInMap = p_ballot.getWriteIns().get(l_contestIndex);
		
		//For each rank
		for (int l_i = 0; l_i < c_choices.length; l_i++)
		{
			//Replace each contestant with the correct Write-In number
			for (int l_j = 0; l_j < c_choices[l_i].length; l_j++)
			{
				int l_k = c_choices[l_i][l_j]; 
				if (l_writeInMap.containsKey(l_k))
				{
					c_choices[l_i][l_j] = l_writeInMap.get(l_k);
				}
			}
		}*/	
		
	}	
	
	public void normalizeChoiceWriteIn(int p_oldId, int p_newId)
	{
		for( int x = 0; x < c_choices.length; x++ )
		{
			for( int y = 0; y < c_choices[x].length; y++ )
			{
				if( c_choices[x][y] == p_oldId )
				{
					c_choices[x][y] = p_newId;
				}
			}
		}
	}
}
