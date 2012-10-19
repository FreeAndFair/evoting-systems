package org.scantegrity.authoring;

import java.awt.Color;
import java.awt.geom.Point2D;
import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.OutputStream;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.Vector;

import com.itextpdf.text.BaseColor;
import com.itextpdf.text.Paragraph;
import com.itextpdf.text.Rectangle;
import com.itextpdf.text.pdf.PdfContentByte;
import com.itextpdf.text.pdf.PdfImportedPage;
import com.itextpdf.text.pdf.PdfLayer;
import com.itextpdf.text.pdf.PdfReader;
import com.itextpdf.text.pdf.PdfWriter;

import org.scantegrity.common.BallotGeometry;
import org.scantegrity.common.Cluster;

/**
 * Produces two files with drill coordinates in the paper. Thse files will get to
 * the machinist and he read them and drill holes.
 * @author stefan
 *
 */
public class Drills {

	static String drillFile1="drill1.txt"; 
	static String drillFile2="drill2.txt";

	static float pageWidth=8.5f*72;
	static float pageHeight=11f*72;
	static float holeDiameter=0.25f*72f;
	
	/**
	 * reads the geometry and calls 
	 * convert(BallotGeometry geometry,String preamble,String pathToDrillsFile,double xShift,double yShift) throws Exception { 
	 */
	public static void GeometryToDrillFile(String pathToBallotMapFile,String pathToDrillsFile,double xShift,double yShift) throws Exception {
		BallotGeometry ballotMap = new BallotGeometry(pathToBallotMapFile);
		Drills.GeometryToDrillFile(ballotMap, pathToDrillsFile,xShift,yShift);
	}
	
	/**
	 * Creates two drill files: one for the upper half of the ballot and one for the lower part
	 *  
	 * From the geometry it extracts where the serial number and the letters on the
	 * bottom pages are and each one hole for each.
	 * 
	 * If can shift the holes by a given amount (in inches)
	 * 
	 * @param geometry - the geometry of the ballot.
	 * @param preamble - the header of the files
	 * @param pathToDrillsFile - a folder where the two files are written
	 * @param xShift - x shifting applied before writing
	 * @param yShift - y shifting applied before writing
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown
	 */
	public static void GeometryToDrillFile(BallotGeometry geometry,String pathToDrillsFile,double xShift,double yShift) throws Exception {
		String note="This is a PunchScan ballot. The diameter of a hole is "+String.format("%.3f",geometry.getHoleDiameter())+" inches";
		String newLine = System.getProperty("line.separator");
		
	    Date today = new Date();
	    SimpleDateFormat formatter = new SimpleDateFormat("MM/dd/yy");
	    String datenewformat = formatter.format(today);    
	    
		String preamble = "(PunchScan Ballot Drill File)" + newLine +
		"(Name supplied by author: \"MadeByStefan\")" + newLine +
		"(File creation Date: "+datenewformat+")" + newLine +
		"(Size: "+String.format("%.3f",geometry.getWidth())+"\" x "+String.format("%.3f",geometry.getHeight())+"\")" + newLine +
		"(NOTE: " + note + ")" + newLine +
		"(Absolute origin upper left corner of unfolded paper)" + newLine +
		"(File format: ANSI/ICP-NC-349 Excellon)" + newLine;		
		
		double w=geometry.getWidth();
		double h=geometry.getHeight();
		
		Vector<Cluster> holesAll = new Vector<Cluster>();
		//The alignment marks do not have holes anymore
		//holesAll.addAll(ballotMap.getAlignmentMap());
		holesAll.addAll(geometry.getSerialBottomClusters());
		/*
		if (ballotMap.getHoleOnly()!=null)
			holesAll.addAll(ballotMap.getHoleOnly());
		*/
		holesAll.addAll(geometry.getContestBottomHoles());

		Vector<Cluster> holesUp = new Vector<Cluster>();
		Vector<Cluster> holesDown = new Vector<Cluster>();
		
		for (Cluster c:holesAll) {
			double x=c.getCenterOfMass().getX();
			double y=c.getCenterOfMass().getY();
			c.setCenterOfMass(new Point2D.Double(x+xShift,y+yShift));
			if (c.getCenterOfMass().getY()<=h/2) 
				holesUp.add(c);
			else
				holesDown.add(c);
		}
		
		//add the clipboard hole
		Cluster clipboardHole=new Cluster();
		clipboardHole.setCenterOfMass(new Point2D.Double(w-0.35,0.35));
		holesUp.add(clipboardHole);
		
		//sort
		Cluster temp;
		boolean sort=false;;
		while (!sort) {
			sort=true;
			for (int i=0;i<holesDown.size()-1;i++) {
				if (holesDown.get(i).getCenterOfMass().getY()>holesDown.get(i+1).getCenterOfMass().getY()) {
					temp=holesDown.get(i);
					holesDown.set(i,holesDown.get(i+1));
					holesDown.set(i+1,temp);
					sort=false;
				} else 
				if (holesDown.get(i).getCenterOfMass().getY()==holesDown.get(i+1).getCenterOfMass().getY()) {
					if (holesDown.get(i).getCenterOfMass().getX() < holesDown.get(i+1).getCenterOfMass().getX()) {
						temp=holesDown.get(i);
						holesDown.set(i,holesDown.get(i+1));
						holesDown.set(i+1,temp);
						sort=false;						
					}
				}
			}
		}

		sort=false;
		while (!sort) {
			sort=true;
			for (int i=0;i<holesUp.size()-1;i++) {
				if (holesUp.get(i).getCenterOfMass().getY()<holesUp.get(i+1).getCenterOfMass().getY()) {
					temp=holesUp.get(i);
					holesUp.set(i,holesUp.get(i+1));
					holesUp.set(i+1,temp);
					sort=false;
				} else
				if (holesUp.get(i).getCenterOfMass().getY()==holesUp.get(i+1).getCenterOfMass().getY()) {
					if (holesUp.get(i).getCenterOfMass().getX()>holesUp.get(i+1).getCenterOfMass().getX()) {					
						temp=holesUp.get(i);
						holesUp.set(i,holesUp.get(i+1));
						holesUp.set(i+1,temp);
						sort=false;
					}
				}				
			}
		}
		
		for (Cluster c:holesDown) {
			Point2D.Double p=c.getCenterOfMass();
			p.setLocation(p.getY(),-(w-p.getX()));
		}

		for (Cluster c:holesUp) {
			Point2D.Double p=c.getCenterOfMass();
			p.setLocation(h-p.getY(),-p.getX());
		}
		
		write(preamble, holesDown, pathToDrillsFile+"/"+drillFile1);		
		write(preamble, holesUp, pathToDrillsFile+"/"+drillFile2);
	}
	
	/**
	 * Creates an industry standard drill file, with a preamble and the coordinates for the holes
	 * @param preamble - a header that is written first to the file
	 * @param holesAll - the coordinates of the holes
	 * @param pathToDrillsFile - whre the file is written
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown
	 */
	private static void write(String preamble, Vector<Cluster> holesAll,String pathToDrillsFile) throws IOException {
		String newLine = System.getProperty("line.separator");
		OutputStream fos = new BufferedOutputStream(new FileOutputStream(pathToDrillsFile));
		fos.write(preamble.getBytes());
		fos.write(("%"+newLine).getBytes());
		fos.write(("M3"+newLine).getBytes());
		Point2D.Double current=null;
		int counter=12;
		String prefix="N";
		for (Cluster c:holesAll) {
			current=new Point2D.Double(c.getCenterOfMass().getX(), c.getCenterOfMass().getY());
			fos.write((prefix+counter).getBytes());
			fos.write(("Y"+String.format("%.3f", current.getY())).getBytes());
			fos.write(("X"+String.format("%.3f", current.getX())).getBytes());
			counter++;
			fos.write(newLine.getBytes());
		}
		fos.write(("%"+newLine).getBytes());
		
		fos.close();		
	}
	
	public static void DrillFilesToPdf(String inDir,String background, String outFile) throws Exception {
		Vector<Point2D.Float> allHoles=new Vector<Point2D.Float>();
		Vector<Point2D.Float> holes;
		
		holes=read(new BufferedReader(new FileReader(inDir+"/"+drillFile1)));
		//corect them, zero is down
		for (int i=0;i<holes.size();i++) {
			Point2D.Float p=holes.get(i);
			p.setLocation(pageWidth+p.getY()*72, p.getX()*72);
		}
		allHoles.addAll(holes);
		holes=read(new BufferedReader(new FileReader(inDir+"/"+drillFile2)));
		for (int i=0;i<holes.size();i++) {
			Point2D.Float p=holes.get(i);
			p.setLocation((-p.getY())*72, pageHeight-p.getX()*72);
		}
		allHoles.addAll(holes);
		
		Rectangle pageSize=new Rectangle(pageWidth,pageHeight);
		
		com.itextpdf.text.Document document = new com.itextpdf.text.Document(pageSize);		
        PdfWriter writer = PdfWriter.getInstance(document, new FileOutputStream(outFile));        
        document.open();
        PdfContentByte cb = writer.getDirectContent();
        
        if (background!=null) {
        	try {
	        	PdfReader reader = new PdfReader(background);
	        	PdfImportedPage page1 = writer.getImportedPage(reader, 1);
	        	cb.beginLayer(new PdfLayer("layer" + Math.random(), writer));
	        	cb.addTemplate(page1,0,0);
	        	cb.endLayer();
        	}catch (Exception e) {
        		;
        	}
        }
        
        document.setMargins(0,0,0,0);
        
        document.add(new Paragraph("Hole diameter "+(holeDiameter/72)+" inches"));
        
        cb.setLineWidth(0.2f);
      // Amir editing
  //      cb.setColorFill(new BaseColor(Color.BLACK));
	//	cb.setColorStroke(new BaseColor(Color.BLACK));

      cb.setColorFill(new BaseColor(0,0,0));
		cb.setColorStroke(new BaseColor(0,0,0));

		float sqrt2r=holeDiameter/2/(float)Math.sqrt(2);
				
    	cb.beginLayer(new PdfLayer("layer" + Math.random(), writer));
		float x,y;
		for (Point2D.Float p:allHoles) {
			x=(float)p.getX();
			y=pageHeight-(float)p.getY();
			
			cb.circle(x,y,holeDiameter/2);
			
			cb.moveTo(x-sqrt2r, y+sqrt2r);
			cb.lineTo(x+sqrt2r,y-sqrt2r);
			cb.moveTo(x-sqrt2r, y-sqrt2r);
			cb.lineTo(x+sqrt2r, y+sqrt2r);
			
			cb.stroke();
		}
		cb.endLayer();
		document.close();
	}

	private static Vector<Point2D.Float> read(BufferedReader in) throws IOException {
		Vector<Point2D.Float> ret= new Vector<Point2D.Float>();
		
		String s=in.readLine();
		while (s.compareTo("M3")!=0) {
			s=in.readLine();
			if (s.startsWith("(Size:")) {
				//read the size
				pageWidth=72f*Float.parseFloat(s.substring(s.indexOf(" "),s.indexOf("\"")).trim());
				pageHeight=72f*Float.parseFloat(s.substring(s.indexOf("x")+1,s.lastIndexOf("\"")).trim());
			}
			if (s.endsWith(" inches)")) {
				s=s.substring(0,s.indexOf(" inches)"));
				//get HoleDiameter
				holeDiameter=72f*Float.parseFloat(s.substring(s.lastIndexOf(" ")));
			}
		}
		s=in.readLine();
		float y,x;
		while (s.compareTo("%")!=0) {
			y=Float.parseFloat(s.substring(s.indexOf("Y")+1, s.indexOf("X")));
			x=Float.parseFloat(s.substring(s.indexOf("X")+1));
			ret.add(new Point2D.Float(x,y));
			s=in.readLine();
		}
		return ret;
	}	
	
	
	/**
	 * @param args
	 * @throws Exception 
	 */
	public static void main(String[] args) throws Exception {
		Drills.GeometryToDrillFile("Elections/VoComp/PunchScan/geometry.xml","Elections/VoComp/PunchScan/",0,0);
		//Drills.DrillFilesToPdf("Elections/VoComp/PunchScan/", null/*"Elections/VoComp/PunchScan/VoComp Sample ballot PunchScan.pdf"*/, "Elections/VoComp/PunchScan/PdfReCreated.pdf");
		//Drills.DrillFilesToPdf("Elections/VoComp/PunchScan/", "Elections/VoComp/PunchScan/VoComp Sample ballot PunchScan.pdf", "Elections/VoComp/PunchScan/PdfReCreated.pdf");
		Drills.DrillFilesToPdf("Elections/VoComp/PunchScan/", "Elections/VoComp/PunchScan/0.pdf", "Elections/VoComp/PunchScan/PdfReCreated.pdf");
	}
}
