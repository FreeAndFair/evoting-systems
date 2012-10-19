package org.scantegrity.common;

import java.awt.Color;
import java.awt.Graphics;
import java.awt.Point;
import java.awt.geom.Point2D;
import java.awt.image.BufferedImage;
import java.io.File;
import java.util.LinkedList;
import java.util.Vector;

import javax.imageio.ImageIO;

import org.scantegrity.common.ScannedBallot;

/**
 * Given an image, it finds all color spots (Clusters) on that image.
 * 
 * It created a private copy of the image that is modified as a new cluster is found. 
 * 
 * Improvments can be made to not have a private copy of the image (same important memory)
 * 
 * @author stefan
 *
 */
public class ImageToCoordinatesInches {
	BufferedImage img;
	Vector<Cluster> sought;

	int filterBackgroundColor = Color.WHITE.getRGB();
	int filterForegroundColor = Color.WHITE.getRGB();
	
	//in pixels
	int x,y;
	
	int column;
	
	private int stepX = 2;
	private int stepY = 2;
	
	int fromx=0;
	int fromy=0;
	int tox;
	int toy;
	
	int numberOfColumns = 1;
	double dpi=1;
	
	/**
	 * The discountinuity of the color spots is given in INCHES.
	 * 
	 * A private copy of the image is made internally. The original image is not modified
	 * @param b The image to be scanned
	 * @param dpi the dpi of the image
	 * @param collorsSougth - the collors to look for. Cannot contain white (it run run out of memory - stack), as
	 * the color used for marking a pixel as visited is white.
	 */	
	public ImageToCoordinatesInches(BufferedImage b,double dpi,Vector<Cluster> collorsSougth) {
		//FIXME make a copy of the image
		//int[] pixels = b.getRGB(0,0,b.getWidth(),b.getHeight(),null,0,b.getWidth());
		img = b;//new BufferedImage(b.getWidth(),b.getHeight(),b.getType());
		//img.setRGB(0,0,img.getWidth(),img.getHeight(),pixels,0,img.getWidth());
		//these are the cluter colors that we are looking for
		this.sought = collorsSougth;
		//the current possition is 0
		x=0;
		y=0;
		column = 0;
		//we will look at the entire image
		tox=b.getWidth();
		toy=b.getHeight();
		//we will measure in inches
		this.dpi=dpi;
	}
	/**
	 * Returns the next cluster found. The search is made by column. The width of
	 * the image is equally divided by the numberOfColumns, so all columns have the same width.
	 * If a cluster is found in one column, it will not be found in another one.
	 * 
	 * @return - the next cluster found or null if no more clusters are found
	 */	
	public Cluster getNextCluster() {
		if (column==numberOfColumns)
			return null;
		Cluster c = getCluster(column);
		if (c!=null)
			return c;
		if (column<numberOfColumns) {
				column++;
				y=fromy;
				x=fromx+column*((tox-fromx)/numberOfColumns);
				return getNextCluster();
		}
		return null;
	}
	
	private Cluster getCluster(int columnNumber) {
		int xmax = fromx+(columnNumber+1)*((tox-fromx)/numberOfColumns);
		int index = -1;
		for (int j=y;j<toy;j+=stepY) {
			for (int i=x;i<xmax;i+=stepX) {
				Color color = new Color((img.getRGB(i,j) << 8) >> 8);
				if ((index = isGivenColor(color)) >=0 ) {
					x=i;
					y=j;
					Cluster c =  clusterBreathFirst(i,j,sought.get(index));
					c.setName(sought.get(index).getName());
					c.setColor(sought.get(index).getColor());
					c.setColorVariation(sought.get(index).getColorVariation());
					return c;
				}
			}
			x=fromx+columnNumber*((tox-fromx)/numberOfColumns);
		}
		return null;
	}
		
	private Cluster clusterBreathFirst(int i, int j,Cluster sougth) {

		Color sougthCollor = sougth.getColor();
		Color sougthVariation= sougth.getColorVariation();
		int sougthDiscountinuity = Math.max(2,(int)Math.round((sougth.getDiscountinuity()*dpi)));
		
		int xmin=i,ymin=j,xmax=i,ymax=j;
		int numberofPoints = 0;
		
		LinkedList<Point> l = new LinkedList<Point>();
		l.add(new Point(i,j));
		img.setRGB(i,j,filterBackgroundColor);
		int x,y;
		int massX = i, massY = j, n=1;
		while( ! l.isEmpty()) {
			Point p = l.remove();			
			for (int ii=1-sougthDiscountinuity;ii<sougthDiscountinuity;ii++) {
				if (p.x+ii >= 0 && p.x+ii < img.getWidth()) {
					x = p.x+ii;
					for (int jj=1-sougthDiscountinuity;jj<sougthDiscountinuity;jj++) {
						if (p.y+jj >= 0 && p.y+jj < img.getHeight()) {
							y = p.y+jj;
							if (isGivenColor(sougthCollor,new Color(img.getRGB(x,y)),sougthVariation)) {
								if (x<xmin) xmin = x;
								if (x>xmax) xmax = x;
								if (y<ymin) ymin = y;
								if (y>ymax) ymax = y;
								numberofPoints++;
								l.add(new Point(x,y));
								img.setRGB(x,y,filterForegroundColor);
								massX +=x;
								massY +=y;
								n++;
							} else {
								img.setRGB(x,y,filterBackgroundColor);
							}
						}
					}
				}
			}			
		}
		Cluster c= new Cluster();
		c.setXmax(xmax/dpi);
		c.setXmin(xmin/dpi);
		c.setYmax(ymax/dpi);
		c.setYmin(ymin/dpi);
		c.setNumberofPoints(numberofPoints/dpi);
		c.setCenterOfMass(new Point2D.Double((c.xmax+c.xmin)/2,(c.ymax+c.ymin)/2));
//		c.setCenterOfMass(new Point2D.Double((xmax+xmin)/2/dpi,(ymax+ymin)/2/dpi));
		return c;
	}

	/** 
	 * @param sougthCollor
	 * @param given
	 * @param deviation
	 * @return true if the distance between two colors is smaller then the deviation
	 * The disatnce is considered on each RGB component separately
	 */
	public static boolean isGivenColor(Color sougthCollor,Color given,Color deviation) {
/*		
		//The sum of the deviations for all the collors whould be smaller them a treshold
		if ( ((Math.abs(sought.getRed() - given.getRed()) + Math.abs(sought.getGreen()-given.getGreen()) + Math.abs(sought.getBlue()-given.getBlue()))) < deviation.getRed() + deviation.getGreen() + deviation.getBlue() )
			return true;
*/

		//Deviation per each collor should b smaller then a treshold
		if (Math.abs(given.getRed() - sougthCollor.getRed()) <= deviation.getRed() &&
				Math.abs(given.getGreen() - sougthCollor.getGreen()) <= deviation.getGreen() &&
				Math.abs(given.getBlue() - sougthCollor.getBlue()) <= deviation.getBlue())
			return true;
		return false;
	}

	private int isGivenColor(Color given) {
		for (int i=0;i<sought.size();i++) {
			Color sougthCollor = sought.get(i).getColor();
			Color deviation = sought.get(i).getColorVariation();
			//Deviation per each collor should be smaller then a treshold
			if (Math.abs(given.getRed() - sougthCollor.getRed()) <= deviation.getRed() &&
					Math.abs(given.getGreen() - sougthCollor.getGreen()) <= deviation.getGreen() &&
					Math.abs(given.getBlue() - sougthCollor.getBlue()) <= deviation.getBlue())
				return i;
			}
		return -1;
	}

	public int getFromx() {
		return fromx;
	}

	public void setFromx(int fromx) {
		this.fromx = fromx;
		x=fromx;
	}

	public int getFromy() {
		return fromy;
	}

	public void setFromy(int fromy) {
		this.fromy = fromy;
		y=fromy;
	}

	public int getNumberOfColumns() {
		return numberOfColumns;
	}

	public void setNumberOfColumns(int numberOfColumns) {
		this.numberOfColumns = numberOfColumns;
	}

	public int getTox() {
		return tox;
	}

	public void setTox(int tox) {
		this.tox = tox;
	}

	public int getToy() {
		return toy;
	}

	public void setToy(int toy) {
		this.toy = toy;
	}

	public int getColumn() {
		return column;
	}

	public BufferedImage getImg() {
		return img;
	}

	/**
	 * Looks for a cluster in concentric circles, starting from the center 
	 * @param startx - the X coordinate of the center
	 * @param starty - the Y coordinate of the center
	 * @param halfSide - the radius of the disk to search
	 * @param sougthCollor1 - the color shougth
	 * @return - the first cluster found in the given color
	 */
	public Cluster detectCircular(double startx, double starty, double halfSide,Cluster sougthCollor1 ) {
		
		int sx=(int)(startx*dpi);
		int sy=(int)(starty*dpi);
		int hs=(int)(halfSide*dpi);

		//FIXME create a copy of the image
		
		int disc=(int)(sougthCollor1.getDiscountinuity()*dpi);
		Cluster sougthCollor=sougthCollor1.clone();
		sougthCollor.setDiscountinuity(0.02);

		
		if (ScannedBallot.debug)
			try {
				int x=Math.max(0,sx-hs);
				int y=Math.max(0, sy-hs);
				int w=Math.min(2*hs, img.getWidth()-x);
				int h=Math.min(2*hs, img.getHeight()-y);
System.out.println(x);				
System.out.println(y);
System.out.println(w);
System.out.println(h);
				BufferedImage subimage=img.getSubimage(x, y, w,h);
				Graphics g=subimage.getGraphics();
				g.setColor(Color.RED);
				g.drawLine(sx-10, sy-10, sx+10, sy+10);
				g.drawLine(sx+10, sy-10, sx-10, sy+10);
				ImageIO.write(subimage, "png", new File("DetectCircular_"+sx+"_"+sy+".png"));
			} catch (Exception e) {
				e.printStackTrace();
			}
		
		
		int x=0;
		int y=0;

//System.out.println((sx+x)+" "+(sy+y));
//System.out.println(sougthCollor.getColor()+ " "+ new Color(img.getRGB(sx+x,sy+y))+ " "+sougthCollor.getColorVariation());		
		
		if (isGivenColor(sougthCollor.getColor(),new Color(img.getRGB(sx+x,sy+y)),sougthCollor.getColorVariation())) {
			return clusterBreathFirst(sx+x,sy+y,sougthCollor);			
		}		
		for (int i=disc;i<hs;i+=disc) {
			//check the lower line
			try {
				y=i;
				for (x=-i;x<=i;x+=disc) {
					if (isGivenColor(sougthCollor.getColor(),new Color(img.getRGB(sx+x,sy+y)),sougthCollor.getColorVariation())) {
						return clusterBreathFirst(sx+x,sy+y,sougthCollor);			
					}
				}
			} catch (java.lang.ArrayIndexOutOfBoundsException e) {}
		
			//checl the left line			
			try {
				x=-i;
				for (y=-i;y<=i;y+=disc) {
					if (isGivenColor(sougthCollor.getColor(),new Color(img.getRGB(sx+x,sy+y)),sougthCollor.getColorVariation())) {
						return clusterBreathFirst(sx+x,sy+y,sougthCollor);			
					}				
				}
			} catch (java.lang.ArrayIndexOutOfBoundsException e) {}
			
			//checl the right line
			try {
				x=i;
				for (y=-i;y<=i;y+=disc) {
					if (isGivenColor(sougthCollor.getColor(),new Color(img.getRGB(sx+x,sy+y)),sougthCollor.getColorVariation())) {
						return clusterBreathFirst(sx+x,sy+y,sougthCollor);		
					}				
				}
			} catch (java.lang.ArrayIndexOutOfBoundsException e) {}
			//checl the upperline
			try {
				y=-i;
				for (x=-i;x<=i;x+=disc) {
					if (isGivenColor(sougthCollor.getColor(),new Color(img.getRGB(sx+x,sy+y)),sougthCollor.getColorVariation())) {
						return clusterBreathFirst(sx+x,sy+y,sougthCollor);			
					}
				}	
			} catch (java.lang.ArrayIndexOutOfBoundsException e) {}
		}		
		return null;
	}
}
