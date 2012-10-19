/* @(#)ContestChoiceIterator.java
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

import java.util.Arrays;
import java.util.Vector;

/**
 * ContestChoiceIterator
 * 
 * Iterates over a ContestChoice object.
 * 
 * @author Rick Carback
 *
 */
public class ContestChoiceIterator {
	/** TODO: The first returned value is the leftmost in the grid. It may be 
	 * necessary to make this configurable.
	 */
	
	
	ContestChoice c_choice;
	//byte c_rules = 0;
	int c_current = -1;
	
	/**
	 * Constructor - creates an invalid object.
	 */
	public ContestChoiceIterator()
	{
		c_choice = null;
	}
	
	/**
	 * Copy Constructor
	 * 
	 * @param p_choiceIterator
	 */
	public ContestChoiceIterator(ContestChoiceIterator p_choiceIterator)
	{
		c_choice = new ContestChoice(p_choiceIterator.c_choice);
		//c_rules = p_choiceIterator.c_rules;
		c_current = p_choiceIterator.c_current;
	}
	
	/**
	 * Constructor - creates an Iterator object for the given ContestChoice. 
	 * The first returned value is the leftmost in the grid. 
	 *  
	 * @param p_choice the choice object.
	 * param p_rules the rules for this object.
	 */
	public ContestChoiceIterator(ContestChoice p_choice)
	{
		c_choice = p_choice;
		//p_rules = 0;
	}
	
	/**
	 * Get the contest choice object used by this Iterator.
	 * @return
	 */
	public ContestChoice getChoice() {
		return c_choice;
	}

	/**
	 * Set/replace the contestchoice object. This function resets the 
	 * iterator. 
	 * 
	 * @param p_choice
	 */
	public void setChoice(ContestChoice p_choice) {
		c_choice = p_choice;
		c_current = -1;
	}

	/**
	 * Get the rules for this ContestChoiceIterator.
	 * 
	 * @return
	 *
	public byte getRules() {
		return c_rules;
	}

	/**
	 * Set the rules for this ContestChoiceIterator. This function will 
	 * not reset the iterator. 
	 * 
	 * @param p_rules
	 *
	public void setRules(byte p_rules) {
		c_rules = p_rules;
	}
	*/
	/**
	 * Get the current ranking. This will not change the state of the iterator.
	 * 
	 * @return
	 */
	public int getCurrent() {
		return c_current;
	}

	/**
	 * Set the current ranking. This will not reset the iterator.
	 * @param p_current
	 */
	public void setCurrent(int p_current) {
		c_current = p_current;
	}	
	
	/**
	 * Iteration function.
	 * 
	 * @param p_badIds List of invalid (disqualified) candidates.
	 * @return
	 */
	public Vector<Integer> getNext(Vector<Integer> p_cans)
	{
		/** TODO: These rules are static. They should be configurable based on
		 * the type of race. Currently, they comply directly with Takoma Park 
		 * election rules. These rules are:
		 * 	- No Duplicates (return a blank object instead). This rule does
		 *		not count when the other duplicates are eliminated before 
		 *		reaching that rank.  
		 *  - Skip one rank (if the voter left a whole rank blank).
		 *  - Ignore/skip defeated candidates.
		 */
		Vector<Integer> l_res = new Vector<Integer>();
		//  v - The Rank
		int[][] l_choices = c_choice.getChoices();
		//    ^ - The candidate ID
		int l_current;
		int l_skip = 0;
		
		if (c_current == -1) l_current = 0;
		else l_current = c_current+1;
		
		//System.out.println(Arrays.deepToString(l_choices));
		while (l_current < l_choices.length)
		{
			for (int l_i = 0; l_i < l_choices[l_current].length; l_i++)
			{
				int l_can = l_choices[l_current][l_i];
				if (l_can == -1) l_skip++;
				else
				{
					//Reset skip
					l_skip = 0;
					//Skip defeated candidates, only add good ones
					if (p_cans.contains(l_can)) l_res.add(l_can);
				}		
			}
			if (l_res.size() > 0 || l_skip > 1) break;
			else l_current++;
		}
		
		c_current = l_current;
		//System.out.print(c_choice.getId() + ": ");
		//System.out.print(l_res.toString() + " ");
		return l_res;
	}
}
