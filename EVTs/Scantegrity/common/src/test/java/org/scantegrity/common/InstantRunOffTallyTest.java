/*
 * @(#)InstantRunOffTallyTest.java.java
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

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.URL;
import java.util.TreeMap;
import java.util.Vector;

import org.junit.Test;
import org.scantegrity.common.Ballot;
import org.scantegrity.common.Contest;
import org.scantegrity.common.Contestant;
import org.scantegrity.common.methods.ContestChoice;
import org.scantegrity.common.methods.IRVContestResult;
import org.scantegrity.common.methods.InstantRunoffTally;

/**
 * Uses IRV test data from Choice Plus on the tally system.
 * @author Richard Carback
 *
 */
public class InstantRunOffTallyTest
{
	static String tests[] = { "http://scantegrity.org/svn/test-data/edata/cpp/cpp",
						"http://scantegrity.org/svn/test-data/edata/misc/tied" 
					};
	
	public static Contest getContestInfo(String l_fname)
	{
		Contest l_contest = new Contest();
		try
		{
			URL l_fread = new URL(l_fname);
			
			l_contest.setContestName(l_fname);
			l_contest.setId(0);
			l_contest.setMethod(new InstantRunoffTally());
			Vector<Contestant> l_contestants = new Vector<Contestant>();
			int l_i = 0;
			BufferedReader l_reader;
			l_reader = new BufferedReader(new InputStreamReader(l_fread.openStream()));
			String l_str;
			while ((l_str = l_reader.readLine()) != null)
			{
				l_contestants.add(new Contestant(l_i, l_str));
				l_i++;
			}
			l_contest.setContestants(l_contestants);
		}
		catch (FileNotFoundException e)
		{
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		catch (IOException e)
		{
			// TODO Auto-generated catch block
			e.printStackTrace();
		}		

		return l_contest;
	}
	
	public static Vector<Ballot> getData(String l_fname)
	{
		URL l_fread;
		Vector<Ballot> l_ballots = new Vector<Ballot>();
		/*
		BallotStyle l_style = new BallotStyle(0, true);
		Vector<Vector<Integer>> l_contestantMap = new Vector<Vector<Integer>>();
		l_contestantMap.add(new Vector<Integer>());
		l_contestantMap.elementAt(0).add(0);
		l_contestantMap.elementAt(0).add(1);
		l_contestantMap.elementAt(0).add(2);
		l_contestantMap.elementAt(0).add(3);
		l_contestantMap.elementAt(0).add(4);
		l_contestantMap.elementAt(0).add(5);
		l_contestantMap.elementAt(0).add(6);
		l_contestantMap.elementAt(0).add(7);
		l_contestantMap.elementAt(0).add(8);
		l_contestantMap.elementAt(0).add(9);
		l_style.setContestantIds(l_contestantMap);
		Vector<Integer> l_cids = new Vector<Integer>();
		
		l_cids.add(0);
		l_style.setContests(l_cids);*/
		
		try
		{
			l_fread = new URL(l_fname);
			BufferedReader l_reader;
			l_reader = new BufferedReader(new InputStreamReader(l_fread.openStream()));
			//Throw away top line
			l_reader.readLine();
			String l_line[];
			String l_str;
			int l_no = 2;
			while ((l_str = l_reader.readLine()) != null)
			{
				l_line = l_str.split(" ");
				if (l_line.length < 1) continue; //Next line
				Integer[][] l_bdata = new Integer[10][10];
				for (int l_i = 0; l_i < 10; l_i++)
				{
					for (int l_j = 0; l_j < 10; l_j++)
					{
						l_bdata[l_i][l_j] = 0;
					}
				}
				
				for (int l_i = 1; l_i < l_line.length; l_i++)
				{
					int l_end = l_line[l_i].indexOf(",");
					if (l_end == -1) l_end = l_line[l_i].length();
					l_line[l_i] = l_line[l_i].substring(0, l_end);
					int l_tmp = Integer.parseInt(l_line[l_i]);
					if (l_tmp-1 >= 0 && l_tmp-1 < 10) 
					{
						l_bdata[l_tmp-1][l_i-1] = 1;
					} 
					else
					{
						System.out.print("Line " + l_no + ": ");
						System.out.println(l_tmp + " is not a valid rank!");
					}
				}

				Ballot l_ballot = new Ballot();
				l_line[0] = l_line[0].substring(0, l_line[0].indexOf(")"));

				l_ballot.setId(Integer.parseInt(l_line[0]));
				//System.out.println("Ballot: " + l_ballot.getId());
				//for (Integer l_b[] : l_bdata)
				//{
				//	System.out.println(java.util.Arrays.toString(l_b));
				//}
				TreeMap<Integer, Integer[][]> l_raw;
				l_raw = new TreeMap<Integer, Integer[][]>();
				l_raw.put(0, l_bdata);
				l_ballot.setBallotData(l_raw);
				l_ballot.setBallotStyleID(0);
				l_ballot.setCounted(true);

				l_ballots.add(l_ballot);
				l_no++;
			}
		}
		catch (FileNotFoundException e)
		{
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		catch (IOException e)
		{
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		return l_ballots;
	}
	/**
	 * @param args
	 */
	@Test
	public void test()
	{
		Vector<Ballot> l_ballots;
		Vector<ContestChoice> l_choices;
		BallotStyle l_style = new BallotStyle();
		Contest l_contest;
		System.out.println("Chad should win. The other will report bob based on him being the last calculated winner.");
		System.out.println("If you make changes to the InstantRunoffTally.java file, you should verify that the full results have not changed.");
		for (int l_i = 0; l_i < tests.length; l_i++)
		{
			System.out.println(tests[l_i] + ":");
			l_ballots = getData(tests[l_i] + ".data");
			l_contest = getContestInfo(tests[l_i] + ".info");
			l_choices = new Vector<ContestChoice>();
			for (int l_j = 0; l_j < l_ballots.size(); l_j++)
			{
				l_choices.add(new ContestChoice(l_j,
												l_ballots.get(l_j),
												l_style, l_contest));
			}
			
			InstantRunoffTally l_tally = new InstantRunoffTally();
			IRVContestResult l_x = (IRVContestResult)l_tally.tally(l_contest, l_choices);
			
			//System.out.println(l_x.toString());
			TreeMap<Integer, Vector<Contestant>> l_c = l_x.getRanking();
			System.out.println(l_c.get(l_c.firstKey()).toString());
		}
	}
}
