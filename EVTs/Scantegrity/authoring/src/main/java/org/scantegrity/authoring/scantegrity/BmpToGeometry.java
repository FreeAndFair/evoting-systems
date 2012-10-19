package org.scantegrity.authoring.scantegrity;

import java.awt.Color;
import java.awt.image.BufferedImage;
import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.util.Vector;

import javax.imageio.ImageIO;

import org.scantegrity.authoring.BmpTogeometryInterface;
import org.scantegrity.common.BallotGeometry;
import org.scantegrity.common.Cluster;
import org.scantegrity.common.ImageToCoordinatesInches;
import org.scantegrity.common.InputConstants;

/**
 * TODO make a special color for rank. This way, when a table (3X3)
 * can be distingueshed between a rank contest and a 1 out of n contacts
 * displayed as a table. 
 */

public class BmpToGeometry implements BmpTogeometryInterface {
	public Vector<Cluster> ScantegrityColors=null;
	
	public BmpToGeometry() {
		ScantegrityColors=new Vector<Cluster>();
		
		Color colorVariation = new Color(20,20,20);
		double colorDiscountinuity = 0.015;//INCHES
		
		
		Cluster c=null;
		//Takoma Park November 3, 2009 takomaMockBallot_apr2009draft11.bmp
		c = new Cluster(new Color(251,0,7),colorVariation,colorDiscountinuity);
		c.setName("serialLatin");
		ScantegrityColors.add(c);

		c = new Cluster(new Color(79,14,203),colorVariation,colorDiscountinuity);
		c.setName("serialBulleted");
		ScantegrityColors.add(c);
		
		c=new Cluster(new Color(0,0,255),colorVariation,colorDiscountinuity);
		c.setName("alignment");
		ScantegrityColors.add(c);
		
		c = new Cluster(new Color(42,255,0),colorVariation,colorDiscountinuity);
		c.setName("candidate1");
		ScantegrityColors.add(c);
		
		c = new Cluster(new Color(255,255,0),colorVariation,colorDiscountinuity);
		c.setName("candidate2");
		ScantegrityColors.add(c);
		
/*		
		Cluster c=null;
		//Takoma Park takomaMockBallot_apr2009draft11.bmp
		c = new Cluster(new Color(191,0,0),colorVariation,colorDiscountinuity);
		c.setName("serialLatin");
		ScantegrityColors.add(c);

		c = new Cluster(new Color(0,127,0),colorVariation,colorDiscountinuity);
		c.setName("serialBulleted");
		ScantegrityColors.add(c);
		
		c=new Cluster(new Color(0,255,251),colorVariation,colorDiscountinuity);
		c.setName("alignment");
		ScantegrityColors.add(c);
		
		c = new Cluster(new Color(217,24,0),colorVariation,colorDiscountinuity);
		c.setName("candidate1");
		ScantegrityColors.add(c);
		
		c = new Cluster(new Color(26,58,253),colorVariation,colorDiscountinuity);
		c.setName("candidate2");
		ScantegrityColors.add(c);
*/		
/*		
		//Takoma Park takomaMockBallot_apr2009draft11.bmp
		c = new Cluster(new Color(243,102,33),colorVariation,colorDiscountinuity);
		c.setName("serialLatin");
		ScantegrityColors.add(c);

		c = new Cluster(new Color(41,192,199),colorVariation,colorDiscountinuity);
		c.setName("serialBulleted");
		ScantegrityColors.add(c);
		
		c=new Cluster(new Color(0,0,251),colorVariation,colorDiscountinuity);
		c.setName("alignment");
		ScantegrityColors.add(c);
		
		c = new Cluster(new Color(55,255,0),colorVariation,colorDiscountinuity);
		c.setName("candidate1");
		ScantegrityColors.add(c);
		
		c = new Cluster(new Color(255,255,0),colorVariation,colorDiscountinuity);
		c.setName("candidate2");
		ScantegrityColors.add(c);
*/
		
/* Capitoll Hill		
		c=new Cluster(new Color(247,255,0),colorVariation,colorDiscountinuity);
		c.setName("alignment");
		ScantegrityColors.add(c);
		
		c = new Cluster(new Color(51,164,87),colorVariation,colorDiscountinuity);
		c.setName("serialLatin");
		ScantegrityColors.add(c);
		
		c = new Cluster(new Color(0,223,214),colorVariation,colorDiscountinuity);
		c.setName("serialBulleted");
		ScantegrityColors.add(c);
		
		c = new Cluster(new Color(227,125,28),colorVariation,colorDiscountinuity);
		c.setName("candidate1");
		ScantegrityColors.add(c);
		
		c = new Cluster(new Color(89,158,194),colorVariation,colorDiscountinuity);
		c.setName("candidate2");
		ScantegrityColors.add(c);
*/
		/*Settings for the Coded Vote vs Plain Vote ballot
		c = new Cluster(new Color(51,164,87),colorVariation,colorDiscountinuity);
		c.setName("serialLatin");
		ScantegrityColors.add(c);

		c = new Cluster(new Color(0,223,214),colorVariation,colorDiscountinuity);
		c.setName("serialBulleted");
		ScantegrityColors.add(c);
		
		c=new Cluster(new Color(247,255,0),colorVariation,colorDiscountinuity);
		c.setName("alignment");
		ScantegrityColors.add(c);
		
		c = new Cluster(new Color(227,125,28),colorVariation,colorDiscountinuity);
		c.setName("candidate1");
		ScantegrityColors.add(c);
		
		c = new Cluster(new Color(89,158,194),colorVariation,colorDiscountinuity);
		c.setName("candidate2");
		ScantegrityColors.add(c);
		*/
/*		
		//Takoma Park Demo11 mock ballot template v 0.2.pdf
		c = new Cluster(new Color(0,234,0),colorVariation,colorDiscountinuity);
		c.setName("serialLatin");
		ScantegrityColors.add(c);

		c = new Cluster(new Color(81,255,189),colorVariation,colorDiscountinuity);
		c.setName("serialBulleted");
		ScantegrityColors.add(c);
		
		c=new Cluster(new Color(208,249,0),colorVariation,colorDiscountinuity);
		c.setName("alignment");
		ScantegrityColors.add(c);
		
		c = new Cluster(new Color(249,86,0),colorVariation,colorDiscountinuity);
		c.setName("candidate1");
		ScantegrityColors.add(c);
		
		c = new Cluster(new Color(31,67,255),colorVariation,colorDiscountinuity);
		c.setName("candidate2");
		ScantegrityColors.add(c);
		
*/
		/*
		//Takoma Park rough AIGA style ballot1.pdf
		c = new Cluster(new Color(243,100,33),colorVariation,colorDiscountinuity);
		c.setName("serialLatin");
		ScantegrityColors.add(c);

		c = new Cluster(new Color(49,191,197),colorVariation,colorDiscountinuity);
		c.setName("serialBulleted");
		ScantegrityColors.add(c);
		
		c=new Cluster(new Color(218,219,33),colorVariation,colorDiscountinuity);
		c.setName("alignment");
		ScantegrityColors.add(c);
		
		c = new Cluster(new Color(141,198,62),colorVariation,colorDiscountinuity);
		c.setName("candidate1");
		ScantegrityColors.add(c);
		
		c = new Cluster(new Color(146,38,143),colorVariation,colorDiscountinuity);
		c.setName("candidate2");
		ScantegrityColors.add(c);
		*/
/*		
		//Takoma Park Demo11 TP2007 2D bardoce.pdf
		c = new Cluster(new Color(51,158,85),colorVariation,colorDiscountinuity);
		c.setName("serialLatin");
		ScantegrityColors.add(c);

		c = new Cluster(new Color(26,168,174),colorVariation,colorDiscountinuity);
		c.setName("serialBulleted");
		ScantegrityColors.add(c);
		
		c=new Cluster(new Color(225,226,60),colorVariation,colorDiscountinuity);
		c.setName("alignment");
		ScantegrityColors.add(c);
		
		c = new Cluster(new Color(216,121,45),colorVariation,colorDiscountinuity);
		c.setName("candidate1");
		ScantegrityColors.add(c);
		
		c = new Cluster(new Color(31,58,255),colorVariation,colorDiscountinuity);
		c.setName("candidate2");
		ScantegrityColors.add(c);
*/
		//GWU mock election
		/*
		c = new Cluster(new Color(0,255,0),colorVariation,colorDiscountinuity);
		c.setName("serialLatin");
		ScantegrityColors.add(c);

		c = new Cluster(new Color(255,0,0),colorVariation,colorDiscountinuity);
		c.setName("serialBulleted");
		ScantegrityColors.add(c);
		
		c=new Cluster(new Color(255,0,255),colorVariation,colorDiscountinuity);
		c.setName("alignment");
		ScantegrityColors.add(c);
		
		c = new Cluster(new Color(0,0,255),colorVariation,colorDiscountinuity);
		c.setName("candidate1");
		ScantegrityColors.add(c);
		
		c = new Cluster(new Color(205,101,50),colorVariation,colorDiscountinuity);
		c.setName("candidate2");
		ScantegrityColors.add(c);
		 */		
	}
	
	public void createGeometry(BufferedImage bi, float dpi, int noCols, String geometryFile,String electionSpecFile) throws Exception {
		float w=bi.getWidth()/dpi;
		float h=bi.getHeight()/dpi;
		BallotGeometry geom=new BallotGeometry(w,h);
		
		
		ImageToCoordinatesInches itc = new ImageToCoordinatesInches(bi,dpi,ScantegrityColors);		
		itc.setNumberOfColumns(noCols);
		itc.setTox((int)(itc.getTox()*1));
		
		Cluster c;
		
		Vector<Cluster> serialLatin=new Vector<Cluster>();
		Vector<Cluster> top=new Vector<Cluster>();
		
		Cluster serialBarcode=null;
		Cluster serialBulleted=null;
		
		int qno=0;
		
		int whichContest=1;
		
		while ((c=itc.getNextCluster()) != null) {	
			//if (c.getXmax()-c.getXmin() > 0.1 && c.getYmax()-c.getYmin() > 0.1) 
			{
System.out.println(c);				
				if (c.getName().startsWith("candidate")) {
					if ((whichContest==1 && c.getName().endsWith("1")) || (whichContest==2 && c.getName().endsWith("2"))) {
							top.add(c);
					} else {
						geom.addContest(qno,top,null);
						qno++;						
						top = new Vector<Cluster>();
						if (whichContest==1)
							whichContest=2;
						else
							whichContest=1;
						top.add(c);
					}					
				} else {
					if (c.getName().compareTo("serialLatin")==0) {
						serialLatin.add(c);
					} else {
						if (c.getName().compareTo("serialBarcode")==0) {
							if (serialBarcode!=null)
								throw new Exception("A second zone for the barcode has been detected/n.First zone "+serialBarcode+"/mSecond Zone "+c);
							serialBarcode=new Cluster(c);
						} else {
							if (c.getName().compareTo("serialBulleted")==0) {
								if (serialBulleted!=null)
									throw new Exception("A second zone for the serialBuleted has been detected/n.First zone "+serialBulleted+"/mSecond Zone "+c);
								serialBulleted=new Cluster(c);
							} else {							
								if (c.getName().compareTo("alignment")==0) {
									geom.addAlignment(c);
								}
							}
						}
					}
				}
			}
		}
		//add the very last contest
		
		geom.addContest(qno,top,null);
		
		//add the serial numbers
		BallotGeometry.sortOnX(serialLatin,0,serialLatin.size());
		geom.setSerial(serialLatin,null);
		
		//add the serial barcode
		if (serialBarcode!=null)
			geom.setSerialBarcode(serialBarcode);
		
		//add the serial bulleted
		geom.setSerialBulleted(serialBulleted);

		OutputStream fos;
		if (geometryFile!=null)
		try {
			fos = new BufferedOutputStream(new FileOutputStream(geometryFile));
			geom.write(fos);
			fos.close();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
		catch (IOException e1) {
			e1.printStackTrace();
		}
		
		if(electionSpecFile!=null)
		try {
			fos = new BufferedOutputStream(new FileOutputStream(electionSpecFile));
			fos.write(geom.getDefaultElectionSpec().toString().getBytes());
			fos.close();
			
			fos = new BufferedOutputStream(new FileOutputStream(new File(electionSpecFile).getParent()+"/partitions.xml"));
			fos.write(geom.getDefaultPartitions().getBytes());
			fos.close();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
		catch (IOException e1) {
			e1.printStackTrace();
		}
		
	}
	
	public Vector<Cluster> getAllColors() {
		return ScantegrityColors;
	}
	
	public static void main(String args[]) throws Exception {
		String dir=InputConstants.publicFolder+"ward6/";
		BmpToGeometry btg = new BmpToGeometry();
		BufferedImage bi = ImageIO.read(new File(dir+"background.bmp"));
		btg.createGeometry(bi, 300, 1, dir+"geometry.xml",dir+"ElectionSpec.xml");
	}
	
}