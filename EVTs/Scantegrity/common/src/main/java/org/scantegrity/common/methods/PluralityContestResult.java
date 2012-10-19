/*
 * @(#)PluralityContestResult.java.java
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

import java.io.UnsupportedEncodingException;
import java.net.URLEncoder;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Vector;

import org.scantegrity.common.Contestant;

/**
 * @author John Conway
 *
 */
public class PluralityContestResult extends ContestResult
{
	Vector<Integer> c_totals;
	
	/**
	 *  Create a new plurality contest result
	 */
	public PluralityContestResult()
	{
		super();
		c_totals = null;
	}
	
	
	
	/**
	 * @return the totals
	 */
	public Vector<Integer> getTotals()
	{
		return c_totals;
	}

	/**
	 * @param p_totals the totals to set
	 */
	public void setTotals(Vector<Integer> p_totals)
	{
		c_totals = p_totals;
	}
	
	public String toString()
	{
		String l_res = "";
		l_res += String.format("%26s", "CANDIDATE");
		l_res += String.format("%26s", "VOTES");
		l_res += "\n----------------------------------------------------\n\n";
		
		Integer l_key = super.c_ranking.firstKey();
		int l_i = 0;
		while (l_key != null)
		{
			Vector<Contestant> ll_contestants = super.c_ranking.get(l_key);
			for( Contestant ll_con : ll_contestants )
			{
				l_res += String.format("%26s", ll_con.getName());
				l_res += String.format("%26d", c_totals.get(l_i));
				l_res += "\n";
			}
			l_key = super.c_ranking.higherKey(l_key);
			l_i++;
		}
		
		return l_res;
	}

	@Override
	public String getHtmlResults(boolean p_includeWebResources)
	{
		ArrayList<Integer> l_graphVotes = new ArrayList<Integer>();
		ArrayList<String> l_graphLabels = new ArrayList<String>();
		int l_total = 0;
		String l_res = "";
		Integer l_key = super.c_ranking.firstKey();
		int l_i = 0;
		l_res = "<table style=\"width: 100%; text-align: left;\">";
		l_res += "<tr><th>Candidate</th><th>Votes</th>";
		while (l_key != null)
		{
			Vector<Contestant> ll_contestants = super.c_ranking.get(l_key);
			for( Contestant ll_con : ll_contestants )
			{
				l_res += "<tr><td>" + ll_con.getName() + "</td>";
				l_res += "<td>" + c_totals.get(l_i) + "</td></tr>";
				l_total += c_totals.get(l_i);
				l_graphVotes.add(c_totals.get(l_i));
				l_graphLabels.add(ll_con.getName());
			}
			l_key = super.c_ranking.higherKey(l_key);
			l_i++;
		}
		l_res += "</table>";
		
		if( p_includeWebResources )
		{
			DecimalFormat onePlace = new DecimalFormat("0.0");
			String l_chart = "http://chart.apis.google.com/chart?";
			String l_chartOpts = "chs=600x200&cht=p3&chd=t:";
	
			for( Integer l_data : l_graphVotes )
			{
				l_chartOpts += onePlace.format(l_data / ((float)l_total));
				l_chartOpts += ",";
			}
			l_chartOpts = l_chartOpts.substring(0, l_chartOpts.length() - 1); //Trim last comma
			l_chartOpts += "&amp;chl=";
			
			for( String l_label : l_graphLabels )
			{
				try {
					l_chartOpts += URLEncoder.encode(l_label, "UTF-8");
				} catch (UnsupportedEncodingException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				l_chartOpts += "|";
			}
			l_chartOpts = l_chartOpts.substring(0, l_chartOpts.length() - 1); //Trim last pipe
			
			l_chart += l_chartOpts;
			
			l_res += "<img src=\"" + l_chart + "\" />";
		}
		
		return l_res;
	}
	
	
}
