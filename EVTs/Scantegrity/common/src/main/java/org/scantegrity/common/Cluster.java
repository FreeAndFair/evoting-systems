package org.scantegrity.common;

import java.awt.Color;
import java.awt.geom.AffineTransform;
import java.awt.geom.Point2D;
import java.io.Serializable;
import java.util.Enumeration;
import java.util.Hashtable;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;

/**
 * A cluster has a center of mass, is in a rectangle of coordonates ((xmin,ymin),(xmax,ymax))
 * and containes a number of points (different from the number of points in the rectangle)
 * A cluster is only a wrapper around those values 
 * @author Stefan
 *
 */
public class Cluster implements Serializable {
	private static final long serialVersionUID = -6351735187914972705L;
	
	String name= "dot";
	double xmin,xmax,ymin,ymax;
	double numberofPoints;
	Point2D.Double centerOfMass = null;
	Color color = null;
	Color colorVariation = null;
	double discountinuity = 0;
	
	Hashtable extraParams = new Hashtable();
	
	/**
	 * empty constructor
	 */
	public Cluster() {
	}
	
	/**
	 * Clones a current Cluster
	 * @param model
	 */
	public Cluster(Cluster model) {
		this();
		this.name = new String(model.getName());
		this.xmin = model.getXmin();
		this.xmax = model.getXmax();
		this.ymin = model.getYmin();
		this.ymax = model.getYmax();
		this.numberofPoints = model.getNumberofPoints(); 
		if (model.getCenterOfMass() != null)
			this.centerOfMass = new Point2D.Double(model.getCenterOfMass().x, model.getCenterOfMass().y);
		else 
			this.centerOfMass = null;
		if (model.getColor() != null)
			this.color = new Color(model.getColor().getRGB());
		else
			this.color = null;
		if (model.getColorVariation() != null) 
			this.colorVariation = new Color(model.getColorVariation().getRGB());
		else
			this.colorVariation = null;
		this.discountinuity = model.getDiscountinuity();
	}
	/**
	 * cluster without a center of mass, only for colors (used in authoring)
	 * @param color
	 * @param colorVariation
	 * @param discountinuity
	 */
	public Cluster(Color color, Color colorVariation, double discountinuity) {
		this();
		this.color = new Color(color.getRGB());
		this.colorVariation = new Color(colorVariation.getRGB());
		this.discountinuity = discountinuity;
	}
	/**
	 * constructs a cluster from an xml node (many elements can be missing)
	 * @param dotNode
	 */	
	public Cluster(Node dotNode) {
		this();
		
		if (dotNode==null) return;
		
		setName(dotNode.getNodeName());
		NamedNodeMap attr = dotNode.getAttributes();
		if (attr.getNamedItem("x") != null)
			setCenterOfMass(new Point2D.Double(Double.parseDouble(attr.getNamedItem("x").getNodeValue()),Double.parseDouble(attr.getNamedItem("y").getNodeValue())));
		if (attr.getNamedItem("fromx") != null)
			setXmin(Double.parseDouble(attr.getNamedItem("fromx").getNodeValue()));
		if (attr.getNamedItem("tox") != null)
			setXmax(Double.parseDouble(attr.getNamedItem("tox").getNodeValue()));
		if (attr.getNamedItem("fromy") != null)
			setYmin(Double.parseDouble(attr.getNamedItem("fromy").getNodeValue()));
		if (attr.getNamedItem("toy") != null) 
			setYmax(Double.parseDouble(attr.getNamedItem("toy").getNodeValue()));
		if (attr.getNamedItem("noPoints") != null)
			setNumberofPoints(Double.parseDouble(attr.getNamedItem("noPoints").getNodeValue()));
		if (attr.getNamedItem("color") != null) {
			setColor(new Color(Integer.parseInt(attr.getNamedItem("color").getNodeValue(),16)));
		}
		if (attr.getNamedItem("colorVariation") != null) {
			setColorVariation(new Color(Integer.parseInt(attr.getNamedItem("colorVariation").getNodeValue(),16)));
		}
		if (attr.getNamedItem("discountinuity") != null) {
			setDiscountinuity(Double.parseDouble(attr.getNamedItem("discountinuity").getNodeValue()));
		}
	}
	/** 
	 * @param affine applies this affine transformation to all the geometrical elements of a cluster
	 */	
	public void affineTransform(AffineTransform affine) {
		double[] src = {xmin,ymin,xmax,ymax,centerOfMass.x,centerOfMass.y};
		affine.transform(src,0,src,0,src.length);
		xmin = src[0];
		ymin = src[1];
		xmax = src[2];
		ymax = src[3];
		centerOfMass = new Point2D.Double(src[4],src[5]);
	}	
	
	/** 
	 * scales the center of mass
	 * @param scalling
	 */
	public void scale(double scalling) {
		AffineTransform rotation = AffineTransform.getScaleInstance(scalling,scalling); 
		rotation.transform(centerOfMass,centerOfMass);

/*		
		xmin *= scalling;
		ymin *= scalling;
		xmax *= scalling;
		ymax *= scalling;
		centerOfMass.setLocation(centerOfMass.getX()*scalling,centerOfMass.getY()*scalling);
*/		
	}
	
	/**
	 * rotates the center of mass
	 * @param pivot - the center of rotation
	 * @param alpha
	 */
	public void rotate(Point2D.Double pivot, double alpha) {
		AffineTransform rotation = AffineTransform.getRotateInstance(alpha,pivot.getX(),pivot.getY());
		rotation.transform(centerOfMass,centerOfMass);
		
/* hand made, not advised		
		Point p2 = centerOfMass;
		Point p1 = pivot;
		double gamma = 0;
		if (p2.x == p1.x)
			gamma = Math.PI / 2;
		else
			gamma = Math.atan((p1.getY()-p2.getY())/(p2.getX()-p1.getX()));

		if (gamma < 0)
			gamma += Math.PI;
			
		double distance = p1.distance(p2);
		
		System.out.println("distance "+p1+" "+p2+" is "+distance);
		
		double x = p1.getX()+distance * Math.cos(alpha+gamma);
		double y = p1.getY()-distance * Math.sin(alpha+gamma);
		p2.setLocation(x,y);
*/		
	}
	
	/**
	 * translates the center of mass
	 * @param tx
	 * @param ty
	 */
	public void translate(double tx,double ty) {
		AffineTransform rotation = AffineTransform.getTranslateInstance(tx,ty); 
		rotation.transform(centerOfMass,centerOfMass);
		
/*		
		xmin += tx;
		ymin += ty;
		xmax += tx;
		ymax += ty;
		centerOfMass.setLocation(centerOfMass.getX()+tx,centerOfMass.getY()+ty);
*/		
	}
	
	/**
	 * Returns a new Cluster, with the same fields as this one
	 */
	public Cluster clone() {
		return new Cluster(this);
	}
	
	/** 
	 * @param c
	 * @return the distance between the center of mass of this cluster and the parameter
	 */
	public double distance(Cluster c) {
		return centerOfMass.distance(c.getCenterOfMass());
	}

	/**
	 * An xml representation of the cluster
	 */
	public String toString() {
		//return name;
		return toXMLString();
	}
	
	/** 
	 * @return	An xml representation of the cluster
	 */
	public String toXMLString() {
		String s="";
		s+="<"+name;
		if (centerOfMass != null)
			s+=" x=\""+String.format("%.3f",centerOfMass.getX())+"\" y=\""+String.format("%.3f",centerOfMass.getY())+"\"";
		if (xmin!=0)
			s+=" fromx=\""+String.format("%.3f",xmin)+"\" fromy=\""+String.format("%.3f",ymin)+"\" tox=\""+String.format("%.3f",xmax)+"\" toy=\""+String.format("%.3f",ymax);
		if (numberofPoints != 0)
			s+="\" noPoints=\""+String.format("%.3f",numberofPoints)+"\"";
		if (color != null)
			s+=" color=\""+Cluster.toHex(color)+"\"";
		if (colorVariation !=null)
			s+=" colorVariation=\""+Cluster.toHex(colorVariation)+"\"";
		if (discountinuity != 0) {
			s+=" discountinuity=\""+String.format("%.3f",discountinuity)+"\"";			
		}
		if (extraParams.size()>0) {
			for (Enumeration e=extraParams.keys();e.hasMoreElements();) {
				Object k = e.nextElement();
				Object v = extraParams.get(k);
				s+=" "+k+"=\""+v+"\"";				
			}
		}
		s+="/>";
		return s;
	}	
	
	public Point2D.Double getCenterOfMass() {
		return centerOfMass;
	}
	public void setCenterOfMass(Point2D.Double centerOfMass) {
		this.centerOfMass = centerOfMass;
	}
	public double getNumberofPoints() {
		return numberofPoints;
	}
	public void setNumberofPoints(double numberofPoints) {
		this.numberofPoints = numberofPoints;
	}
	public double getXmax() {
		return xmax;
	}
	public void setXmax(double xmax) {
		this.xmax = xmax;
	}
	public double getXmin() {
		return xmin;
	}
	public void setXmin(double xmin) {
		this.xmin = xmin;
	}
	public double getYmax() {
		return ymax;
	}
	public void setYmax(double ymax) {
		this.ymax = ymax;
	}
	public double getYmin() {
		return ymin;
	}
	public void setYmin(double ymin) {
		this.ymin = ymin;
	}

	public Color getColor() {
		return color;
	}

	public void setColor(Color color) {
		this.color = color;
	}

	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}
	
	public Color getColorVariation() {
		return colorVariation;
	}

	public void setColorVariation(Color colorVariation) {
		this.colorVariation = colorVariation;
	}

	public double getDiscountinuity() {
		return discountinuity;
	}

	public void setDiscountinuity(double discountinuity) {
		this.discountinuity = discountinuity;
	}
	
	public Element getNodeXY(Document doc) {
		Element t=doc.createElement(name);
		t.setAttribute("x",String.format("%.3f",centerOfMass.getX()));
		t.setAttribute("y",String.format("%.3f",centerOfMass.getY()));
		return t;
	}
	
	public Element getNodeXYFromTo(Document doc) {
		Element t=doc.createElement(name);
		t.setAttribute("x",String.format("%.3f",centerOfMass.getX()));
		t.setAttribute("y",String.format("%.3f",centerOfMass.getY()));
		t.setAttribute("fromx",String.format("%.3f",xmin));
		t.setAttribute("fromy",String.format("%.3f",ymin));
		t.setAttribute("tox",String.format("%.3f",xmax));
		t.setAttribute("toy",String.format("%.3f",ymax));
		return t;
	}	
	
	public static String toHex(Color c) {
		String red = Integer.toHexString(c.getRed());
		if (red.length() < 2)
			red = "0"+red;
		String green = Integer.toHexString(c.getGreen());
		if (green.length() < 2)
			green = "0"+green;
		String blue = Integer.toHexString(c.getBlue());
		if (blue.length() < 2)
			blue = "0"+blue;
		return red+green+blue;	
	}	
}
