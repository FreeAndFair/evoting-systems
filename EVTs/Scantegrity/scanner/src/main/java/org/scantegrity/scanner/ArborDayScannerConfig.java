/*
 * @(#)CreateScannerConfig.java.java
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
package org.scantegrity.scanner;

import java.awt.Dimension;
import java.awt.Point;
import java.awt.Rectangle;
import java.beans.XMLEncoder;
import java.io.BufferedOutputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.text.DateFormat;
import java.text.ParseException;
import java.util.TreeMap;
import java.util.Vector;

import org.scantegrity.common.BallotStyle;
import org.scantegrity.common.Contest;
import org.scantegrity.common.Contestant;
import org.scantegrity.common.methods.InstantRunoffTally;
import org.scantegrity.common.methods.PluralityTally;
import org.scantegrity.scanner.CircleAlignmentMarkReader;
import org.scantegrity.scanner.QRCodeReader;
import org.scantegrity.scanner.ScannerConfig;
import org.scantegrity.scanner.ScantegrityBallotReader;

/**
 * Scanner config creator. Translated from Stefan's BallotGeom.xml file.
 * 
 * Unfortunately, don't have a translator module for that just yet.
 * 
 * @author Richard Carback
 *
 */
public class ArborDayScannerConfig
{
	private static String c_loc = "";
	private static String c_name = "ScannerConfig.xml";

	/**
	 * @param args
	 */
	public static void main(String[] args)
	{
		ScannerConfig l_config = new ScannerConfig();
		ScantegrityBallotReader l_reader = new ScantegrityBallotReader();
		
		Dimension l_d = new Dimension(2550, 4200);
		Point[] l_marks = new Point[2];
		l_marks[0] = new Point(2480, 464);
		l_marks[1] = new Point(2498, 3268);
		QRCodeReader l_code = new QRCodeReader();
		l_code.setSerialBoundingBox(new Rectangle(226, 132, 331, 370));
		l_reader.setSerial(l_code);
		l_reader.setAlignment(l_marks);
		l_reader.setDimension(l_d);
		l_reader.setAlignmentMark(new CircleAlignmentMarkReader(80/2, .05));
		l_reader.setTolerance(.4);
		
		Vector<Integer> l_contests = new Vector<Integer>();
		l_contests.add(0);
		l_contests.add(1);
		l_contests.add(2);
		l_contests.add(3);

		Vector<Vector<Vector<Rectangle>>> l_rects = new Vector<Vector<Vector<Rectangle>>>();
		TreeMap<Integer, TreeMap<Integer, Rectangle>> l_writeInRects = new TreeMap<Integer, TreeMap<Integer,Rectangle>>();
		TreeMap<Integer, Rectangle> l_tempMap;
		//Contest 0
		l_rects.add(new Vector<Vector<Rectangle>>());
		l_rects.elementAt(0).add(new Vector<Rectangle>());
		l_rects.elementAt(0).elementAt(0).add(new Rectangle(1582, 762, 146, 51));
		l_rects.elementAt(0).elementAt(0).add(new Rectangle(1776, 762, 146, 51));
		l_rects.elementAt(0).elementAt(0).add(new Rectangle(1960, 762, 146, 51));
		l_rects.elementAt(0).elementAt(0).add(new Rectangle(2158, 762, 146, 51));
		l_rects.elementAt(0).elementAt(0).add(new Rectangle(2357, 762, 146, 51));
		l_rects.elementAt(0).add(new Vector<Rectangle>());
		l_rects.elementAt(0).elementAt(1).add(new Rectangle(1582, 861, 146, 51));
		l_rects.elementAt(0).elementAt(1).add(new Rectangle(1776, 861, 146, 51));
		l_rects.elementAt(0).elementAt(1).add(new Rectangle(1960, 861, 146, 51));
		l_rects.elementAt(0).elementAt(1).add(new Rectangle(2158, 861, 146, 51));
		l_rects.elementAt(0).elementAt(1).add(new Rectangle(2357, 861, 146, 51));
		l_rects.elementAt(0).add(new Vector<Rectangle>());
		l_rects.elementAt(0).elementAt(2).add(new Rectangle(1582, 960, 146, 51));
		l_rects.elementAt(0).elementAt(2).add(new Rectangle(1776, 960, 146, 51));
		l_rects.elementAt(0).elementAt(2).add(new Rectangle(1960, 960, 146, 51));
		l_rects.elementAt(0).elementAt(2).add(new Rectangle(2158, 960, 146, 51));
		l_rects.elementAt(0).elementAt(2).add(new Rectangle(2357, 960, 146, 51));
		l_rects.elementAt(0).add(new Vector<Rectangle>());
		l_rects.elementAt(0).elementAt(3).add(new Rectangle(1582, 1060, 146, 51));
		l_rects.elementAt(0).elementAt(3).add(new Rectangle(1776, 1060, 146, 51));
		l_rects.elementAt(0).elementAt(3).add(new Rectangle(1960, 1060, 146, 51));
		l_rects.elementAt(0).elementAt(3).add(new Rectangle(2158, 1060, 146, 51));
		l_rects.elementAt(0).elementAt(3).add(new Rectangle(2357, 1060, 146, 51));
		l_rects.elementAt(0).add(new Vector<Rectangle>());
		l_rects.elementAt(0).elementAt(4).add(new Rectangle(1582, 1160, 146, 51));
		l_rects.elementAt(0).elementAt(4).add(new Rectangle(1776, 1160, 146, 51));
		l_rects.elementAt(0).elementAt(4).add(new Rectangle(1960, 1160, 146, 51));
		l_rects.elementAt(0).elementAt(4).add(new Rectangle(2158, 1160, 146, 51));
		l_rects.elementAt(0).elementAt(4).add(new Rectangle(2357, 1160, 146, 51));
		l_tempMap = new TreeMap<Integer, Rectangle>(); 
		l_tempMap.put(4, (new Rectangle(1100, 1290, 920, 200)));
		l_writeInRects.put(0, l_tempMap);
		
		//Contest 1
		l_rects.add(new Vector<Vector<Rectangle>>());
		l_rects.elementAt(1).add(new Vector<Rectangle>());
		l_rects.elementAt(1).elementAt(0).add(new Rectangle(1779, 1716, 123, 54));
		l_rects.elementAt(1).elementAt(0).add(new Rectangle(1973, 1716, 123, 54));
		l_rects.elementAt(1).elementAt(0).add(new Rectangle(2166, 1716, 123, 54));
		l_rects.elementAt(1).elementAt(0).add(new Rectangle(2360, 1716, 123, 54));
		l_rects.elementAt(1).add(new Vector<Rectangle>());
		l_rects.elementAt(1).elementAt(1).add(new Rectangle(1779, 1816, 123, 54));
		l_rects.elementAt(1).elementAt(1).add(new Rectangle(1973, 1816, 123, 54));
		l_rects.elementAt(1).elementAt(1).add(new Rectangle(2166, 1816, 123, 54));
		l_rects.elementAt(1).elementAt(1).add(new Rectangle(2360, 1816, 123, 54));
		l_rects.elementAt(1).add(new Vector<Rectangle>());
		l_rects.elementAt(1).elementAt(2).add(new Rectangle(1779, 1916, 123, 54));
		l_rects.elementAt(1).elementAt(2).add(new Rectangle(1973, 1916, 123, 54));
		l_rects.elementAt(1).elementAt(2).add(new Rectangle(2166, 1916, 123, 54));
		l_rects.elementAt(1).elementAt(2).add(new Rectangle(2360, 1916, 123, 54));
		l_rects.elementAt(1).add(new Vector<Rectangle>());
		l_rects.elementAt(1).elementAt(3).add(new Rectangle(1779, 2016, 123, 54));
		l_rects.elementAt(1).elementAt(3).add(new Rectangle(1973, 2016, 123, 54));
		l_rects.elementAt(1).elementAt(3).add(new Rectangle(2166, 2016, 123, 54));
		l_rects.elementAt(1).elementAt(3).add(new Rectangle(2360, 2016, 123, 54));
		
		l_tempMap = new TreeMap<Integer, Rectangle>(); 
		l_tempMap.put(3, (new Rectangle(1100, 2125, 920, 200)));
		l_writeInRects.put(1, l_tempMap);
		
		//Contest 2
		l_rects.add(new Vector<Vector<Rectangle>>());
		l_rects.elementAt(2).add(new Vector<Rectangle>());
		l_rects.elementAt(2).elementAt(0).add(new Rectangle(1592, 2727, 120, 51));
		l_rects.elementAt(2).add(new Vector<Rectangle>());
		l_rects.elementAt(2).elementAt(1).add(new Rectangle(1592, 2827, 120, 51));
		l_rects.elementAt(2).add(new Vector<Rectangle>());
		l_rects.elementAt(2).elementAt(2).add(new Rectangle(1592, 2927, 120, 51));
		l_rects.elementAt(2).add(new Vector<Rectangle>());
		l_rects.elementAt(2).elementAt(3).add(new Rectangle(1592, 3027, 120, 51));
		l_rects.elementAt(2).add(new Vector<Rectangle>());
		l_rects.elementAt(2).elementAt(4).add(new Rectangle(1592, 3127, 120, 51));
		//Contest 3
		l_rects.add(new Vector<Vector<Rectangle>>());
		l_rects.elementAt(3).add(new Vector<Rectangle>());
		l_rects.elementAt(3).elementAt(0).add(new Rectangle(2167, 2924, 123, 55));
		l_rects.elementAt(3).add(new Vector<Rectangle>());
		l_rects.elementAt(3).elementAt(1).add(new Rectangle(2167, 3024, 123, 55));
		
		
		Vector<Vector<Integer>> l_contestantIds = new Vector<Vector<Integer>>();
		l_contestantIds.add(new Vector<Integer>());
		l_contestantIds.get(0).add(0);
		l_contestantIds.get(0).add(1);
		l_contestantIds.get(0).add(2);
		l_contestantIds.get(0).add(3);
		l_contestantIds.get(0).add(4);
		l_contestantIds.add(new Vector<Integer>());
		l_contestantIds.get(1).add(0);
		l_contestantIds.get(1).add(1);
		l_contestantIds.get(1).add(2);
		l_contestantIds.get(1).add(3);
		l_contestantIds.add(new Vector<Integer>());
		l_contestantIds.get(2).add(0);
		l_contestantIds.get(2).add(1);
		l_contestantIds.get(2).add(2);
		l_contestantIds.get(2).add(3);
		l_contestantIds.get(2).add(4);
		l_contestantIds.add(new Vector<Integer>());
		l_contestantIds.get(3).add(0);
		l_contestantIds.get(3).add(1);		
		
		BallotStyle l_style = new BallotStyle(0, l_contests, l_rects, true);
		l_style.setWriteInRects(l_writeInRects);
		l_style.setContestantIds(l_contestantIds);
		BallotStyle l_styles[] = new BallotStyle[1];
		l_styles[0] = l_style;
		
		Vector<Contest> l_c = new Vector<Contest>();
		Contest l_x = new Contest();
		l_x.setId(0);
		l_x.setContestName("<b>Favorite Tree </b><br/><i> Arbol Favorito</i>");
		l_x.setShortName("FavoriteTree");
		Vector<Contestant> l_can = new Vector<Contestant>();
		l_can.add(new Contestant(0, "Cherry / el cerezo"));
		l_can.add(new Contestant(1, "Elm / el olmo"));
		l_can.add(new Contestant(2, "Maple / el arce"));
		l_can.add(new Contestant(3, "Oak / el roble"));
		l_can.add(new Contestant(4, "Write-In / o por escrito"));
		l_x.setContestants(l_can);
		l_x.setMethod(new InstantRunoffTally());
		l_c.add(l_x);

		l_x = new Contest();
		l_x.setId(1);
		l_x.setContestName("<b>Favorite Forest Animal</b><br/><i>Animal Arbolado Favorito</i>");
		l_x.setShortName("FavoriteForestName");
		l_can = new Vector<Contestant>();
		l_can.add(new Contestant(0, "Owl / Buho"));
		l_can.add(new Contestant(1, "Rabbit / Conejo"));
		l_can.add(new Contestant(2, "Squirrel / Ardilla"));
		l_can.add(new Contestant(3, "Write-In / o por escrito"));
		l_x.setContestants(l_can);
		l_x.setMethod(new InstantRunoffTally());
		l_c.add(l_x);		

		l_x = new Contest();
		l_x.setId(2);
		l_x.setContestName("<b>How many trees are on your property?" 
				+ " </b><br/><i> Cuanto arboles estan en su propiedad?</i>");
		l_x.setContestName("NumberTrees");
		l_can = new Vector<Contestant>();
		l_can.add(new Contestant(0, "0"));
		l_can.add(new Contestant(1, "1-2"));
		l_can.add(new Contestant(2, "3-5"));
		l_can.add(new Contestant(3, "6-10"));
		l_can.add(new Contestant(4, "More than 10 / Mas de 10"));
		l_x.setContestants(l_can);
		l_x.setMethod(new PluralityTally());
		l_c.add(l_x);		
		
		l_x = new Contest();
		l_x.setId(3);
		l_x.setContestName("<b>Do you use less paper products than you did ten "
						+ "years ago? </b><br/><i> Utiliza menos producto de papel que" +
						" hace 10 anos?</i>");
		l_x.setShortName("LessPaper");
		l_can = new Vector<Contestant>();
		l_can.add(new Contestant(0, "Yes / Si"));
		l_can.add(new Contestant(1, "No / No"));
		l_x.setContestants(l_can);
		l_x.setMethod(new PluralityTally());
		l_c.add(l_x);		
				
		Vector<String> l_outDirNames = new Vector<String>();
		l_outDirNames.add("/media/");
		
		
		Vector<BallotStyle> l_s = new Vector<BallotStyle>();
		l_s.add(l_style);
		
		Vector<String> l_j = new Vector<String>();
		l_j.add("Anne Sergeant");
		l_config.setChiefJudges(l_j);
		l_config.setLocation("Takoma Park Community Center Azalea Room");
		l_config.setName("Arbor Day Mock Election at Takoma Park");
		l_config.setOutputDirNames(l_outDirNames);
		l_config.setPollID(10);
		l_config.setReader(l_reader);
		l_config.setContests(l_c);
		
		l_config.setDate("April 11, 2009");
		l_config.setTime("10:00 am");
		
		l_config.setScannerID(0);
		l_config.setStyles(l_s);
		
		/*Vector<String> l_jh = new Vector<String>();
		l_jh.add("[B@de6ced");
		l_config.setJudgePassHash(l_jh);*/
		
		XMLEncoder e;
		try
		{
			FileOutputStream l_out = new FileOutputStream(c_loc + "ContestInformation.xml");
			e = new XMLEncoder(new BufferedOutputStream(new FileOutputStream(c_loc + c_name)));
			e.writeObject(l_config);
			e.close();		
			e = new XMLEncoder(new BufferedOutputStream(new FileOutputStream(c_loc + "ContestInformation.xml")));
			e.writeObject(l_c);
			e.close();
		}
		catch (FileNotFoundException e1)
		{
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		
	}

}
