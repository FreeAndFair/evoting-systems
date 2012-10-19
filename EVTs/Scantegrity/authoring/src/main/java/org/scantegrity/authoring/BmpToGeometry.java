package org.scantegrity.authoring;

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

import org.scantegrity.common.BallotGeometry;
import org.scantegrity.common.Cluster;
import org.scantegrity.common.ImageToCoordinatesInches;

/**
 * Reads in an image, detects the bullets and the donuts on it and
 * builds a geometry file (and a default ElectionSpecification)
 * @author stefan
 *
 */
public class BmpToGeometry implements BmpTogeometryInterface {
	public Vector<Cluster> PunchScanColors=null;
	
	/**
	 * Initiates the default color to look for. The color variation is 10 
	 * on each color and the 
	 * discontinuity is 0.01inches. 
	 *
	 */
	public BmpToGeometry() {
		PunchScanColors=new Vector<Cluster>();
		
		Color colorVariation = new Color(10,10,10);
		double colorDiscountinuity = 0.01;//INCHES

		Cluster c=null;
		
		c=new Cluster(new Color(255,255,0),colorVariation,colorDiscountinuity);
		c.setName("alignment");
		PunchScanColors.add(c);
		
		c = new Cluster(new Color(0,127,0),colorVariation,colorDiscountinuity);
		c.setName("serial");
		PunchScanColors.add(c);

		c = new Cluster(new Color(255,205,0),colorVariation,colorDiscountinuity);
		c.setName("candidate1");
		PunchScanColors.add(c);
		
		c = new Cluster(new Color(0,0,255),colorVariation,colorDiscountinuity);
		c.setName("candidate2");
		PunchScanColors.add(c);
	}
	
	public void createGeometry(BufferedImage bi, float dpi, int noCols,String geometryFile,String ElectionSpecFile) throws Exception {
		float w=bi.getWidth()/dpi;
		float h=bi.getHeight()/dpi;
		BallotGeometry geom=new BallotGeometry(w,h);
		
		ImageToCoordinatesInches itc = new ImageToCoordinatesInches(bi,dpi,PunchScanColors);		
		itc.setNumberOfColumns(noCols);
		
		Cluster c;
		
		Vector<Cluster> topSerial=new Vector<Cluster>();
		Vector<Cluster> bottomSerial=new Vector<Cluster>();
		
		Vector<Cluster> top=new Vector<Cluster>();
		Vector<Cluster> bottom=new Vector<Cluster>();
		int qno=0;
		
		int whichContest=1;
		
		while ((c=itc.getNextCluster()) != null) {
//System.out.println(c);			
			if (c.getXmax()-c.getXmin() > 0.05 && c.getYmax()-c.getYmin() > 0.05) {
//System.out.println(c);				
				if (c.getName().startsWith("candidate")) {
					if ((whichContest==1 && c.getName().endsWith("1")) || (whichContest==2 && c.getName().endsWith("2"))) {
						if (isTop(bi,dpi,c)) {
							top.add(c);
						} else {
							bottom.add(c);						
						}
					} else {
						geom.addContest(qno,top,bottom);
						qno++;						
						bottom = new Vector<Cluster>();
						top = new Vector<Cluster>();
						if (whichContest==1)
							whichContest=2;
						else
							whichContest=1;
						if (isTop(bi,dpi,c)) {
							top.add(c);
						} else {
							bottom.add(c);						
						}												
					}					
				} else {
					if (c.getName().compareTo("serial")==0) {
						if (isTop(bi,dpi,c))
							topSerial.add(c);
						else
							bottomSerial.add(c);
					} else {
						if (c.getName().compareTo("alignment")==0) {
							geom.addAlignment(c);
						} else {
							if (c.getName().compareTo("holeOnly")==0) {
								geom.addHoleOnly(c);
							}
						}
					}
				}
			}
		}
		//add the very last contest
		geom.addContest(qno,top,bottom);
		
		//add the serial numbers				
		geom.setSerial(topSerial,bottomSerial);
		
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
		
		if (ElectionSpecFile!=null)
			try {
				fos = new BufferedOutputStream(new FileOutputStream(ElectionSpecFile));
				fos.write(geom.getDefaultElectionSpec().toString().getBytes());
				fos.close();
			} catch (FileNotFoundException e) {
				e.printStackTrace();
			}
			catch (IOException e1) {
				e1.printStackTrace();
			}
	}
	
	private static boolean isTop(BufferedImage img, double dpi,Cluster cluster) {
		//Check if the pixel in the center of mass of the cluster is the same color
		//as the color of the cluster
		
		Color c = new Color(img.getRGB((int)(cluster.getCenterOfMass().x*dpi),(int)(cluster.getCenterOfMass().y*dpi)));
		
		Color varfiation=cluster.getColorVariation();
		if (ImageToCoordinatesInches.isGivenColor(cluster.getColor(),c,new Color(varfiation.getRed()*4,varfiation.getGreen()*4,varfiation.getBlue()*4))) {
			return true;
		}
		return false;
	}

	public Vector<Cluster> getAllColors() {
		return PunchScanColors;
	}
	
	/**
	 * debug method
	 * @param args
	 * @throws Exception
	 */
	public static void main(String args[]) throws Exception {
		String dir="Elections/CPSR/7And1/";
		BmpToGeometry btg=new BmpToGeometry();
		BufferedImage bi = ImageIO.read(new File(dir+"7And1.bmp"));
		btg.createGeometry(bi, 150, 2, dir+"geometry.xml",dir+"ElectionSpec.xml");
	}
	
}