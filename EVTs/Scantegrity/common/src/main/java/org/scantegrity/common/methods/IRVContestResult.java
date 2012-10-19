/*
 * @(#)IRVContestRest.java.java
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

import java.io.StringWriter;
import java.io.UnsupportedEncodingException;
import java.net.URLEncoder;
import java.text.DecimalFormat;
import java.util.Vector;

import org.scantegrity.common.Contestant;

/**
 * 
 * @author Richard Carback
 *
 */
public class IRVContestResult extends ContestResult
{	
	protected Integer c_contestId = -1;
	protected Vector<Contestant> c_contestants = null;
	protected Vector<Round> c_rounds = null;
	
	public IRVContestResult()
	{
		this (-1, null);
	}
	
	/**
	 * @param p_l_rounds
	 */
	public IRVContestResult(Integer p_contestId, 
							Vector<Contestant> p_contestants)
	{
		super();
		c_contestId = p_contestId;
		this.setCandidates(p_contestants);
		c_rounds = new Vector<Round>();		
	}
	
	public void addRound(Round p_round)
	{
		c_rounds.add(p_round);
	}

	/**
	 * @return the l_rounds
	 */
	public Vector<Round> getRounds()
	{
		return c_rounds;
	}

	/**
	 * @param p_l_rounds the l_rounds to set
	 */
	public void setRounds(Vector<Round> p_rounds)
	{
		c_rounds = p_rounds;
	}
	
	/**
	 * @return the candidates
	 */
	public Vector<Contestant> getContestants()
	{
		return c_contestants;
	}
	/**
	 * @param p_candidates the candidates to set
	 */
	public void setCandidates(Vector<Contestant> p_contestants)
	{
		c_contestants = new Vector<Contestant>(p_contestants);
	}
	
	/**
	 * @return the contestId
	 */
	public Integer getContestId()
	{
		return c_contestId;
	}

	/**
	 * @param p_contestId the contestId to set
	 */
	public void setContestId(Integer p_contestId)
	{
		c_contestId = p_contestId;
	}

	public String toString()
	{
		StringWriter l_res = new StringWriter();
		
		for (Round l_r : c_rounds)
		{
			l_res.write(l_r.toString());
		}
		
		return l_res.toString();
	}
	
	@Override
	public String getHtmlResults(boolean p_includeWebResources)
	{
		String l_results = "";
		
		l_results += "<div id='divAllRounds" + c_contestId + "' style='display: none;'>";
		for( int x = 0; x < c_rounds.size(); x++ )
		{
			if( x == c_rounds.size() - 1 )
				l_results += "</div>";
			
			l_results += c_rounds.get(x).getHtmlRound();
			if( p_includeWebResources )
				l_results += getChart(c_rounds.get(x));
		}
		
		if( p_includeWebResources ) l_results += "<br/><a id='viewLink" + c_contestId + "' href='#' onclick=\"javascript:document.getElementById('divAllRounds" + c_contestId + "').style.display='';document.getElementById('viewLink" + c_contestId + "').style.display='none';\">Click here to view intermediate rounds</a><br/>";
		return l_results;
	}
	
	public String getChart(Round p_round)
	{
		DecimalFormat onePlace = new DecimalFormat("0.0");
		String l_chart = "http://chart.apis.google.com/chart?";
		String l_chartOpts = "chs=600x200&cht=p3&chd=t:";
		String l_res = "";
		
		int l_total = 0;
		for( Integer l_data: p_round.getTotals() )
			l_total += l_data;

		for( Integer l_data : p_round.getTotals() )
		{
			l_chartOpts += onePlace.format(l_data / ((float)l_total));
			l_chartOpts += ",";
		}
		l_chartOpts = l_chartOpts.substring(0, l_chartOpts.length() - 1); //Trim last comma
		l_chartOpts += "&amp;chl=";
		
		for( Contestant l_label : c_contestants )
		{
			try {
				l_chartOpts += URLEncoder.encode(l_label.getName(), "UTF-8");
			} catch (UnsupportedEncodingException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			l_chartOpts += "|";
		}
		l_chartOpts = l_chartOpts.substring(0, l_chartOpts.length() - 1); //Trim last pipe
		
		l_chart += l_chartOpts;
		
		l_res += "<img src=\"" + l_chart + "\" />";
		return l_res;
	}
	
	
	public class Round {
		protected int c_id;
		protected String c_desc;
		protected Vector<Integer> c_totals;
		protected Vector<Integer> c_delta;
		protected Vector<String> c_state;
		protected Vector<String> c_roundNotes;

		public Round()
		{
			this(-1, null, null, null, null);
		}
		
		/**
		 * Only used on the first instantiate. The rest should use the
		 * next instantiation.
		 * @param p_id
		 */
		public Round(int p_id)
		{
			c_id = p_id;
			c_totals = new Vector<Integer>();
			c_delta = new Vector<Integer>();
			c_state = new Vector<String>();
			c_roundNotes = new Vector<String>();
			c_desc = "";
			
			c_totals.setSize(c_contestants.size());
			c_delta.setSize(c_contestants.size());
			c_state.setSize(c_contestants.size());
			for (int l_i = 0; l_i < c_state.size(); l_i++)
			{
				if (c_contestants.get(l_i).getId() >= 0)
					c_state.set(l_i, "CONTINUES");
				else
					c_state.set(l_i, "EXHAUST");
			}
		}

		public Round(Round p_prev)
		{
			c_id = p_prev.getId()+1;
			c_totals = new Vector<Integer>(p_prev.getTotals());
			c_delta = new Vector<Integer>();
			c_state = new Vector<String>(p_prev.getState());
			c_roundNotes = new Vector<String>();
			c_desc = new String(p_prev.c_desc);

			c_delta.setSize(c_contestants.size());
		}

		/**
		 * @param p_id
		 * @param p_totals
		 * @param p_delta
		 * @param p_state
		 * @param p_roundNotes
		 */
		public Round(int p_id, Vector<Integer> p_totals, 
				Vector<Integer> p_delta, Vector<String> p_state, 
				Vector<String> p_roundNotes)
		{
			c_id = p_id;
			c_totals = p_totals;
			c_delta = p_delta;
			c_state = p_state;
			c_desc = "";			
			c_roundNotes = p_roundNotes;
		}	
		
		public Round clone()
		{
			Round l_new = new Round(c_id);
			l_new.setDelta(new Vector<Integer>(c_delta));
			l_new.setDesc(new String(c_desc));
			l_new.setId(c_id);
			l_new.setRoundNotes(new Vector<String>(c_roundNotes));
			l_new.setState(new Vector<String>(c_state));
			l_new.setTotals(new Vector<Integer>(c_totals));		
			return l_new;
		}
		
		/**
		 * @return the id
		 */
		public int getId()
		{
			return c_id;
		}
		/**
		 * @param p_id the id to set
		 */
		public void setId(int p_id)
		{
			c_id = p_id;
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
		/**
		 * @return the lastTot
		 */
		public Vector<Integer> getDelta()
		{
			return c_delta;
		}
		/**
		 * @param p_lastTot the lastTot to set
		 */
		public void setDelta(Vector<Integer> p_delta)
		{
			c_delta = p_delta;
		}
		/**
		 * @return the state
		 */
		public Vector<String> getState()
		{
			return c_state;
		}
		/**
		 * @param p_state the state to set
		 */
		public void setState(Vector<String> p_state)
		{
			c_state = p_state;
		}
		/**
		 * @return the roundNotes
		 */
		public Vector<String> getRoundNotes()
		{
			return c_roundNotes;
		}
		/**
		 * @param p_roundNotes the roundNotes to set
		 */
		public void setRoundNotes(Vector<String> p_roundNotes)
		{
			c_roundNotes = p_roundNotes;
		}
		
		public void addNote(String p_note)
		{
			c_roundNotes.add(p_note);
		}
		
		/**
		 * @return the desc
		 */
		public String getDesc()
		{
			return c_desc;
		}

		/**
		 * Desc is a description parameter, which is used to delineate different
		 * paths of execution during an irreconcilable tie.
		 *
		 * @param p_desc the desc to set
		 */
		public void setDesc(String p_desc)
		{
			c_desc = p_desc;
		}

		public String toString()
		{
			StringWriter l_out = new StringWriter();
			int l_change = 0, l_tot = 0;
			//ROUND\t\tCONTESTANTS\t\tCHANGE\t\tTOTALS
			String l_fmt = "\n\nRESULTS FOR ROUND %s%s\n";
			l_out.write(String.format(l_fmt, c_id, c_desc));
			l_out.write("----------------------------------------\n\n");
			l_out.write("\t\tCONTESTANT\t\t\tCHANGE\t\t\tTOTALS\t\t\tSTATE\n");
			l_fmt = "%26s";
			for(int l_i = 0; l_i < c_contestants.size(); l_i++)
			{
				
				l_out.write(String.format(l_fmt, c_contestants.get(l_i)));
				l_out.write(String.format("%+26d", c_delta.get(l_i)));
				l_out.write(String.format(l_fmt, c_totals.get(l_i)));
				l_out.write(String.format(l_fmt, c_state.get(l_i)));
				l_out.write("\n");
				
				l_change += c_delta.get(l_i);
				l_tot += c_totals.get(l_i);
			}
			l_out.write("\n\n");
			l_out.write(String.format(l_fmt, "TOTALS:"));
			l_out.write(String.format("%+26d", l_change));
			l_out.write(String.format(l_fmt, l_tot));
			l_out.write("\n\n");
			for (String note : c_roundNotes) l_out.write(note + "\n");
			
			return l_out.toString();
		}

		public String getHtmlRound()
		{
			StringWriter l_out = new StringWriter();
			int l_change = 0, l_tot = 0;
			//ROUND\t\tCONTESTANTS\t\tCHANGE\t\tTOTALS
			l_out.write("<h4>Round " + getId() + ": ");
			l_out.write("<table style=\"width:100%; text-alignment: left; border: 1px solid black; \">");
			//l_out.write("<tr><th>Contestant</th><th>Change</th><th>Total</th> <th>State</th></tr>");
			l_out.write("<tr><th><em>Contestant</em></th><th><em>Total</em></th><th><em>State</em></th></tr>");
			boolean l_odd = false;
			for(int l_i = 0; l_i < c_contestants.size(); l_i++)
			{
				if (l_odd == false) {
					l_out.write("<tr style=\"background-color:#c3e4c3; border: 1px solid black;\">");
					l_odd = true;
				}
				else {
					l_out.write("<tr>");
					l_odd = false;
				}
				l_out.write("<td style=\"border: 1px solid black;\">" +  c_contestants.get(l_i).getName() + "</td>");
				//l_out.write("<td>" + String.format("%+d", c_delta.get(l_i)) + "</td>");
				l_out.write("<td style=\"border: 1px solid black;\">" +  c_totals.get(l_i) + "</td>");
				l_out.write("<td style=\"border: 1px solid black;\">" +  c_state.get(l_i) + "</td>");
				l_out.write("</tr>");
				
				l_change += c_delta.get(l_i);
				l_tot += c_totals.get(l_i);
			}
			l_out.write("<tr style=\"border: 1px solid black;\">");
			l_out.write("<td style=\"border: 1px solid black;\">Totals:</td>");
			//l_out.write("<td>" + l_change + "</td>");
			l_out.write("<td style=\"border: 1px solid black;\">" + l_tot + "</td><td/>");
			l_out.write("</tr>");
			l_out.write("</table>");
			l_out.write("<p>");
			for (String note : c_roundNotes) l_out.write(note + "<br/>");
			l_out.write("</p>");
			
			return l_out.toString();
		}

	}

}
