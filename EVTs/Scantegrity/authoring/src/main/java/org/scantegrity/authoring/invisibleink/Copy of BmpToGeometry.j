package software.authoring.invisibleink;

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

import software.authoring.BmpTogeometryInterface;
import software.common.BallotGeometry;
import software.common.Cluster;
import software.common.ImageToCoordinatesInches;

public class BmpToGeometry implements BmpTogeometryInterface {
	public Vector<Cluster> ScantegrityColors=null;
	
	public BmpToGeometry() {
		ScantegrityColors=new Vector<Cluster>();
		
		Color colorVariation = new Color(10,10,10);
		double colorDiscountinuity = 0.02;//INCHES

		Cluster c=null;
/*		
		c=new Cluster(new Color(255,255,0),colorVariation,colorDiscountinuity);
		c.setName("alignment");
		ScantegrityColors.add(c);
		
		c = new Cluster(new Color(0,127,0),colorVariation,colorDiscountinuity);
		c.setName("serialLatin");
		ScantegrityColors.add(c);

		c = new Cluster(new Color(255,0,0),colorVariation,colorDiscountinuity);
		c.setName("serialBarcode");
		ScantegrityColors.add(c);
		
		c = new Cluster(new Color(153,51,101),colorVariation,colorDiscountinuity);
		c.setName("serialBulleted");
		ScantegrityColors.add(c);
		
		c = new Cluster(new Color(255,204,0),colorVariation,colorDiscountinuity);
		c.setName("candidate1");
		ScantegrityColors.add(c);
		
		c = new Cluster(new Color(0,0,255),colorVariation,colorDiscountinuity);
		c.setName("candidate2");
		ScantegrityColors.add(c);
		*/
		
		c = new Cluster(new Color(0,127,0),colorVariation,colorDiscountinuity);
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
		
	}
	
	public void createGeometry(BufferedImage bi, float dpi, int noCols, String geometryFile,String electionSpecFile) throws Exception {
		float w=bi.getWidth()/dpi;
		float h=bi.getHeight()/dpi;
		BallotGeometry geom=new BallotGeometry(w,h);
		
		ImageToCoordinatesInches itc = new ImageToCoordinatesInches(bi,dpi,ScantegrityColors);
		
		//TODO remove these
		itc.setFromx((int)(0.4*dpi));//0.3 inches on the left
		itc.setTox((int)((w-0.5)*dpi));//0.3 inches from the right
		
		
		itc.setNumberOfColumns(noCols);
		
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
		//add the very last contest
		geom.addContest(qno,top,null);
		
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
		String dir="D:/PunchScan2.0/PunchScan2.0/Elections/InvisibleInk/CapitolHill/";
		BmpToGeometry btg = new BmpToGeometry();
		BufferedImage bi = ImageIO.read(new File(dir+"policy ballot (rev6).bmp"));
		btg.createGeometry(bi, 300, 2, dir+"geometry.xml",dir+"ElectionSpec.xml");
	}
	
}