/*
 * @(#)ScannerConfigReader.java.java
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
package org.scantegrity.scanner.test;

import java.beans.XMLDecoder;
import java.io.BufferedInputStream;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.util.Vector;

import org.scantegrity.common.BallotStyle;
import org.scantegrity.common.Contest;
import org.scantegrity.common.Contestant;
import org.scantegrity.scanner.BallotReader;
import org.scantegrity.scanner.ScannerConfig;

/**
 * Reads "ScannerConfig.xml"
 * 
 * @author Richard Carback
 *
 */
public class ScannerConfigReader
{
	private static String c_loc = "testing/scanner/";
	private static String c_name = "ScannerConfig.xml";

	/**
	 * @param args
	 */
	public static void main(String[] args)
	{
		// TODO Auto-generated method stub
		ScannerConfig l_config;
		XMLDecoder e;
		try
		{
			e = new XMLDecoder(new BufferedInputStream(new FileInputStream(c_loc + c_name)));
			l_config = (ScannerConfig)e.readObject();
			e.close();		
			
			if (l_config != null)
			{
				System.out.println("Name: " + l_config.getName());
				System.out.println("Chief Judges: " + l_config.getChiefJudges().toString());
				System.out.println("Date: " + l_config.getDate().toString());
				System.out.println("Poll ID: " + l_config.getPollID());
				System.out.println("Scanner ID: " + l_config.getScannerID());
				System.out.println("Reader Options: ");
				BallotReader l_reader = l_config.getReader();
				System.out.println("\tType: " + l_reader.getClass().getName());
				System.out.println("\tDimensions: " + l_reader.getDimension().toString());
				System.out.println("\tAlignmentMarks: " + l_reader.getAlignmentMark().getClass().getName());
				System.out.println("\t\t" + l_reader.getAlignment()[0].toString());
				System.out.println("\t\t" + l_reader.getAlignment()[1].toString());
				System.out.println("\tTolerance: " + l_reader.getTolerance());
				Vector<Contest> l_contests = l_config.getContests();
				System.out.println("Contests");
				for (Contest l_c : l_contests)
				{
					System.out.println("\tName: " + l_c.getContestName());
					System.out.println("\tID: " + l_c.getId());
					System.out.print("\tContestants: ");
					for (Contestant l_s : l_c.getContestants())
					{
						System.out.print(l_s.toString());
					}
					System.out.println("\n\tRace Type: " + l_c.getMethod().getClass().getCanonicalName());
				}
				System.out.println("Output Locations: " + java.util.Arrays.toString(l_config.getOutputDirNames().toArray()));
				Vector<BallotStyle> l_styles = l_config.getStyles();
				System.out.println("Styles");
				for (BallotStyle l_s : l_styles)
				{
					System.out.println("\tID: " + l_s.getId());
					int l_c = 0;
					for (int l_i = 0; l_i < l_s.getContests().size(); l_i++)
					{
						l_c = l_s.getContests().get(l_i);
						System.out.println("\tContest " + l_c);
						System.out.println("\tID Map: " + java.util.Arrays.toString(l_s.getContestantIds().get(l_i).toArray()));
						System.out.println("\tRectangles: " + java.util.Arrays.toString(l_s.getContestRects().get(l_i).toArray()));	
					}
				}
			}
		}
		catch (FileNotFoundException e1)
		{
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		
	}

}
