/*
 * @(#)Contest.java.java
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
package org.scantegrity.common;

import java.io.StringWriter;
import java.util.HashSet;
import java.util.Set;
import java.util.TreeSet;
import java.util.Vector;

import org.scantegrity.common.Contestant.ContestantType;
import org.scantegrity.common.methods.TallyMethod;
/**
 * Contest describes a race, question, or other contest that appears in an 
 * election. This description includes a list of options or names in the contest,
 * an ID number, the rules for this contest, and instructions on how to tally 
 * this contest.
 * 
 * @author Richard Carback
 *
 */
public class Contest
{
	private String c_contestName;
	private Integer c_id;
	private int c_nextId = 0;
	private Vector<Contestant> c_contestants;
	//private MarkRules c_rules;
	private TallyMethod c_method;
	private TreeSet<Integer> c_writeIns = new TreeSet<Integer>(); //Indices in c_contestants that are write-in candidates originally (i.e. candidates named "write-in")
	private TreeSet<Integer> c_resolved = new TreeSet<Integer>(); //Indices in c_contestants that are resolved write-in candidates (i.e. candidates that were not on the ballot)
	private String c_shortName = null;
	
	public Contest() {
		
	}

	/**
	 * Copy Constructor
	 * @param p_contest
	 */
	@SuppressWarnings("unchecked")
	public Contest(Contest p_contest) {
		c_contestName = new String(p_contest.getContestName());
		c_id = new Integer(p_contest.getId()); 
		c_nextId = new Integer(p_contest.getNextId());
		c_contestants = (Vector<Contestant>) p_contest.getContestants().clone();
		c_method = p_contest.getTallyMethod();
		c_writeIns = (TreeSet<Integer>) p_contest.c_writeIns.clone();
		c_resolved = (TreeSet<Integer>) p_contest.c_resolved.clone(); 
		c_shortName = new String(p_contest.getShortName());
	}

	public TallyMethod getTallyMethod()
	{
		return c_method;
	}
	
	public String getShortName()
	{
		return c_shortName;
	}
	
	public void setShortName(String p_shortName)
	{
		c_shortName = p_shortName;
	}
	
	/**
	 * @return the contestName
	 */
	public String getContestName()
	{
		return c_contestName;
	}
	
	public void setContestName(String p_contestName, String p_shortName)
	{
		c_contestName = p_contestName;
		c_shortName = p_shortName;
	}
	
	/**
	 * @param p_contestName the contestName to set
	 */
	public void setContestName(String p_contestName)
	{
		c_contestName = p_contestName;
		c_shortName = p_contestName;
	}
	/**
	 * @return the id
	 */
	public Integer getId()
	{
		return c_id;
	}
	/**
	 * @param p_id the id to set
	 */
	public void setId(Integer p_id)
	{
		c_id = p_id;
	}
	/**
	 * @return the options
	 */
	public Vector<Contestant> getContestants()
	{
		return c_contestants;
	}
	/**
	 * @param p_options the options to set
	 */
	public void setContestants(Vector<Contestant> p_options)
	{
		c_contestants = p_options;
		c_writeIns.clear();
		c_resolved.clear();
		for( int x = 0; x < c_contestants.size(); x++ )
		{
			Contestant l_contestant = c_contestants.get(x);
			if( l_contestant.getId() > c_nextId )
				c_nextId = l_contestant.getId();
			ContestantType l_type = l_contestant.getCandidateType();
			if( l_type == ContestantType.WRITEIN )
			{
				c_writeIns.add(x);
			}
			else if( l_type == ContestantType.RESOLVED )
			{
				c_resolved.add(x);
			}
		}
		c_nextId++;
	}
	
	public void addContestant(Contestant p_new)
	{
		c_contestants.add(p_new);
		if( p_new.getId() >= c_nextId )
		{
			c_nextId = p_new.getId() + 1;
		}
		ContestantType l_type = p_new.getCandidateType();
		if( l_type == ContestantType.WRITEIN )
		{
			c_writeIns.add(c_contestants.indexOf(p_new));
		}
		else if( l_type == ContestantType.RESOLVED )
		{
			c_resolved.add(c_contestants.indexOf(p_new));
		}
	}
	
	public int getNextId()
	{
		return c_nextId;
	}
	/**
	 * @return the rules
	 *//*
	public MarkRules getRules()
	{
		return c_rules;
	}
	/**
	 * @param p_rules the rules to set
	 *//*
	public void setRules(MarkRules p_rules)
	{
		c_rules = p_rules;
	}
	/**
	 * @return the method
	 */
	public TallyMethod getMethod()
	{
		return c_method;
	}
	/**
	 * @param p_method the method to set
	 */
	public void setMethod(TallyMethod p_method)
	{
		c_method = p_method;
	}
	
	public String toString()
	{
		String l_ret = "Contest\n";
		l_ret += "-----------\n";
		l_ret += "Name: " + c_contestName + "\n";
		l_ret += "ID: " + c_id + "\n";
		l_ret += "Contestants:" + "\n";
		for(int x = 0; x < c_contestants.size(); x++ )
		{
			l_ret += c_contestants.get(x).toString() + "\n";
		}
		l_ret += "\n";
		return l_ret;
	}
}
