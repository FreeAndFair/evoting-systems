package org.scantegrity.scanner;

import java.awt.Dimension;
import java.awt.Frame;
import java.awt.Point;
import java.awt.Rectangle;
import java.beans.XMLEncoder;
import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.util.TreeMap;
import java.util.Vector;

import javax.swing.JFileChooser;

import org.scantegrity.common.BallotStyle;
import org.scantegrity.common.Contest;
import org.scantegrity.common.Contestant;
import org.scantegrity.common.methods.InstantRunoffTally;
import org.scantegrity.common.methods.PluralityTally;

public class TakomaConfig 
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
		
		//Dimension of Ballot
		Dimension l_d = new Dimension(2550, 4200);
		
		//The alignment Marks
		Point[] l_marks = new Point[2];
		l_marks[0] = new Point(372, 1576);
		l_marks[1] = new Point(378, 2578);
		
		//Serial Number
		QRCodeReader l_code = new QRCodeReader();
		l_code.setSerialBoundingBox(new Rectangle(2209, 3809, 303, 275));
		l_reader.setSerial(l_code);
		l_reader.setAlignment(l_marks);
		l_reader.setDimension(l_d);
		l_reader.setAlignmentMark(new CircleAlignmentMarkReader(80/2, .05));
		l_reader.setTolerance(.4);
		
		/* ******************************************************
		 * Contest Information
		 ********************************************************/
		
		/* ******************************************************
		 * Ballot Style 0
		 ********************************************************/
		//The contests 
		Vector<Integer> l_contests_0 = new Vector<Integer>();
		l_contests_0.add(0);
		l_contests_0.add(1);

		//Contest Locations
		Vector<Vector<Vector<Rectangle>>> l_rects_0 = new Vector<Vector<Vector<Rectangle>>>();
		TreeMap<Integer, TreeMap<Integer, Rectangle>> l_writeInRects_0 = new TreeMap<Integer, TreeMap<Integer,Rectangle>>();
		TreeMap<Integer, Rectangle> l_tempMap_0;
		
		/* ******************************************************
		 * Contest 0
		 ********************************************************/
		l_rects_0.add(new Vector<Vector<Rectangle>>());
		l_rects_0.elementAt(0).add(new Vector<Rectangle>());
		//row 0
		l_rects_0.elementAt(0).elementAt(0).add(new Rectangle(1582, 762, 146, 51));
		l_rects_0.elementAt(0).elementAt(0).add(new Rectangle(1776, 762, 146, 51));
		l_rects_0.elementAt(0).elementAt(0).add(new Rectangle(1960, 762, 146, 51));
		l_rects_0.elementAt(0).elementAt(0).add(new Rectangle(2158, 762, 146, 51));
		l_rects_0.elementAt(0).elementAt(0).add(new Rectangle(2357, 762, 146, 51));
		//row 1
		l_rects_0.elementAt(0).add(new Vector<Rectangle>());
		l_rects_0.elementAt(0).elementAt(1).add(new Rectangle(1582, 861, 146, 51));
		l_rects_0.elementAt(0).elementAt(1).add(new Rectangle(1776, 861, 146, 51));
		l_rects_0.elementAt(0).elementAt(1).add(new Rectangle(1960, 861, 146, 51));
		l_rects_0.elementAt(0).elementAt(1).add(new Rectangle(2158, 861, 146, 51));
		l_rects_0.elementAt(0).elementAt(1).add(new Rectangle(2357, 861, 146, 51));
		//row 2
		l_rects_0.elementAt(0).add(new Vector<Rectangle>());
		l_rects_0.elementAt(0).elementAt(2).add(new Rectangle(1582, 960, 146, 51));
		l_rects_0.elementAt(0).elementAt(2).add(new Rectangle(1776, 960, 146, 51));
		l_rects_0.elementAt(0).elementAt(2).add(new Rectangle(1960, 960, 146, 51));
		l_rects_0.elementAt(0).elementAt(2).add(new Rectangle(2158, 960, 146, 51));
		l_rects_0.elementAt(0).elementAt(2).add(new Rectangle(2357, 960, 146, 51));
		//row 3
		l_rects_0.elementAt(0).add(new Vector<Rectangle>());
		l_rects_0.elementAt(0).elementAt(3).add(new Rectangle(1582, 1060, 146, 51));
		l_rects_0.elementAt(0).elementAt(3).add(new Rectangle(1776, 1060, 146, 51));
		l_rects_0.elementAt(0).elementAt(3).add(new Rectangle(1960, 1060, 146, 51));
		l_rects_0.elementAt(0).elementAt(3).add(new Rectangle(2158, 1060, 146, 51));
		l_rects_0.elementAt(0).elementAt(3).add(new Rectangle(2357, 1060, 146, 51));
		
		//write in rect
		l_tempMap_0 = new TreeMap<Integer, Rectangle>(); 
		l_tempMap_0.put(4, (new Rectangle(1100, 1290, 920, 200)));
		l_writeInRects_0.put(0, l_tempMap_0);
		
		/* ******************************************************
		 * Contest 1
		 ********************************************************/
		l_rects_0.add(new Vector<Vector<Rectangle>>());
		//row 0 
		l_rects_0.elementAt(1).add(new Vector<Rectangle>());
		l_rects_0.elementAt(1).elementAt(0).add(new Rectangle(1779, 1716, 123, 54));
		l_rects_0.elementAt(1).elementAt(0).add(new Rectangle(1973, 1716, 123, 54));
		l_rects_0.elementAt(1).elementAt(0).add(new Rectangle(2166, 1716, 123, 54));
		l_rects_0.elementAt(1).elementAt(0).add(new Rectangle(2360, 1716, 123, 54));
		//row 1
		l_rects_0.elementAt(1).add(new Vector<Rectangle>());
		l_rects_0.elementAt(1).elementAt(1).add(new Rectangle(1779, 1816, 123, 54));
		l_rects_0.elementAt(1).elementAt(1).add(new Rectangle(1973, 1816, 123, 54));
		l_rects_0.elementAt(1).elementAt(1).add(new Rectangle(2166, 1816, 123, 54));
		l_rects_0.elementAt(1).elementAt(1).add(new Rectangle(2360, 1816, 123, 54));
		//row 2
		l_rects_0.elementAt(1).add(new Vector<Rectangle>());
		l_rects_0.elementAt(1).elementAt(2).add(new Rectangle(1779, 1916, 123, 54));
		l_rects_0.elementAt(1).elementAt(2).add(new Rectangle(1973, 1916, 123, 54));
		l_rects_0.elementAt(1).elementAt(2).add(new Rectangle(2166, 1916, 123, 54));
		l_rects_0.elementAt(1).elementAt(2).add(new Rectangle(2360, 1916, 123, 54));
		//row 3
		l_rects_0.elementAt(1).add(new Vector<Rectangle>());
		l_rects_0.elementAt(1).elementAt(3).add(new Rectangle(1779, 2016, 123, 54));
		l_rects_0.elementAt(1).elementAt(3).add(new Rectangle(1973, 2016, 123, 54));
		l_rects_0.elementAt(1).elementAt(3).add(new Rectangle(2166, 2016, 123, 54));
		l_rects_0.elementAt(1).elementAt(3).add(new Rectangle(2360, 2016, 123, 54));
		
		//write in rect
		l_tempMap_0 = new TreeMap<Integer, Rectangle>(); 
		l_tempMap_0.put(3, (new Rectangle(1100, 2125, 920, 200)));
		l_writeInRects_0.put(1, l_tempMap_0);
		
		//end contest rects 
		
		//add the contestant IDs
		Vector<Vector<Integer>> l_contestantIds_0 = new Vector<Vector<Integer>>();
		l_contestantIds_0.add(new Vector<Integer>());
		l_contestantIds_0.get(0).add(0);
		l_contestantIds_0.get(0).add(1);
		l_contestantIds_0.get(0).add(2);
		l_contestantIds_0.get(0).add(3);
		l_contestantIds_0.add(new Vector<Integer>());
		l_contestantIds_0.get(1).add(0);
		l_contestantIds_0.get(1).add(1);
		l_contestantIds_0.get(1).add(2);
		l_contestantIds_0.get(1).add(3);	
		
		// Add contest to ballot style
		BallotStyle l_style_0 = new BallotStyle(0, l_contests_0, l_rects_0, true);
		l_style_0.setWriteInRects(l_writeInRects_0);
		l_style_0.setContestantIds(l_contestantIds_0);
		
		
		/* ******************************************************
		 * Ballot Style 1
		 ********************************************************/
		//the contests
		Vector<Integer> l_contests_1 = new Vector<Integer>();
		l_contests_1.add(0);
		l_contests_1.add(1);
		
		
		
		/* ******************************************************
		 * Ballot Style 2
		 ********************************************************/
		//the contests
		Vector<Integer> l_contests_2 = new Vector<Integer>();
		l_contests_2.add(0);
		l_contests_2.add(1);
		
		
		
		/* ******************************************************
		 * Ballot Style
		 ********************************************************/
		Vector<BallotStyle> l_s = new Vector<BallotStyle>();
		l_s.add(l_style_0);
		//l_s.add(l_style_1);
		//l_s.add(l_style_2);
		
		
		Vector<Contest> l_c = new Vector<Contest>();
		Contest l_x = new Contest();
		l_x.setId(0);
		l_x.setContestName("<b>Favorite Tree </b><br/><i> Arbol Favorito</i>");
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
		l_can = new Vector<Contestant>();
		l_can.add(new Contestant(0, "Yes / Si"));
		l_can.add(new Contestant(1, "No / No"));
		l_x.setContestants(l_can);
		l_x.setMethod(new PluralityTally());
		l_c.add(l_x);		
		
		Vector<String> l_locs = new Vector<String>();
		l_locs.add("/home/scantegrity/");
		l_locs.add("/media/disk/scantegrity/");
		
		Vector<String> l_outDirName = new Vector<String>();
		l_outDirName.add("/home/scantegrity/");
		
		Vector<String> l_j = new Vector<String>();
		l_j.add("Anne Sergeant");
		l_config.setChiefJudges(l_j);
		l_config.setLocation("Takoma Park Community Center Azalea Room");
		l_config.setName("Arbor Day Mock Election at Takoma Park");
		l_config.setOutputDirNames(l_outDirName);
		l_config.setPollID(10);
		l_config.setReader(l_reader);
		l_config.setContests(l_c);
		
		l_config.setDate("April 11, 2009");
		l_config.setTime("10:00 am");
		
		l_config.setScannerID(0);
		l_config.setStyles(l_s);
		
		XMLEncoder e;
		try
		{
			//scanner config
			JFileChooser l_chooser = new JFileChooser();
			l_chooser.showSaveDialog(new Frame());
			File l_file = l_chooser.getSelectedFile();
			e = new XMLEncoder(new BufferedOutputStream(new FileOutputStream(l_file)));
			e.writeObject(l_config);
			e.close();		
			
			//contest information
			l_chooser.showSaveDialog(new Frame());
			l_file = l_chooser.getSelectedFile();
			e = new XMLEncoder(new BufferedOutputStream(new FileOutputStream(l_file)));
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
