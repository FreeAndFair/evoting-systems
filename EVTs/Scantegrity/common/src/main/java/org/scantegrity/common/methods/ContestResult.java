/*
 * @(#)ContestResult.java.java
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

import java.util.TreeMap;
import java.util.Vector;

import org.scantegrity.common.Contestant;
/**
 * ContestResults represents the results of a Contest. This is, at the basic
 * level, simply a mapping of candidates to their final rankings. Extending 
 * classes store 
 * 
 * @author Rick Carback
 * @param <TreeMap>
 *
 */
public class ContestResult
{
	protected TreeMap<Integer, Vector<Contestant>> c_ranking;

	/**
	 * Create a basic (invalid) ContestResult.
	 */
	public ContestResult() 
	{
		c_ranking = null;
	}
	
	/**
	 * @return the ranking
	 */
	public TreeMap<Integer, Vector<Contestant>> getRanking()
	{
		return c_ranking;
	}

	/**
	 * @param p_ranking the ranking to set
	 */
	public void setRanking(TreeMap<Integer, Vector<Contestant>> p_ranking)
	{
		c_ranking = p_ranking;
	}
	
	/**
	 * This is intended to be overwritten!
	 */
	public String toString()
	{
		String l_res = "";
		l_res += "Ranking\n";
		Integer l_key = c_ranking.firstKey();
		while (l_key != null)
		{
			l_res += l_key + ". " + c_ranking.get(l_key).toString();
			l_key = c_ranking.higherKey(l_key);
		}
		
		return l_res;
	}
	
	public String abbreviatedResults()
	{
		return toString();
	}
	
	public String getHtmlResults(boolean p_includeWebResources)
	{
		return "<pre>" + toString() + "</pre>";
	}
	
	public String getHtmlResults()
	{
		return getHtmlResults(true);
	}
	
}
