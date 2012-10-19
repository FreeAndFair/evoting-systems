package org.scantegrity.common;

/**
 * A holder for the geometry (layout) of the ballot = where are things to be placed:
 * the letters, serial number, alignment marks and extra holes.
 * 
 * It can read an xml file specifying the geometry and it can write it also.
 * @author stefan
 *
 */
import java.awt.geom.Point2D;
import java.io.IOException;
import java.io.OutputStream;
import java.util.Hashtable;
import java.util.TreeMap;
import java.util.Vector;

import org.scantegrity.common.ballotstandards.Constants;
import org.scantegrity.common.ballotstandards.basic.Answer;
import org.scantegrity.common.ballotstandards.basic.Question;
import org.scantegrity.common.ballotstandards.basic.Section;
import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;


import com.itextpdf.text.Rectangle;
import com.sun.org.apache.xml.internal.serialize.OutputFormat;
import com.sun.org.apache.xml.internal.serialize.XMLSerializer;

public class BallotGeometry {

	protected Document doc=null;
	
	protected Element ballot;
	
	protected float width,height;

	double holeDiameter=-1;
	
	/**
	 * Builds a new, blank geometry of size width,height
	 * @param width - the with of the ballot in inches
	 * @param height - the height of the ballot in inches
	 */
	public BallotGeometry(float width,float height) {
		this.width=width;
		this.height=height;

		doc = Util.GetDocumentBuilder().newDocument();
		
		ballot = doc.createElement("ballot");
		ballot.setAttribute("width",String.format("%.3f",width));			
		ballot.setAttribute("heigth",String.format("%.3f",height));
		doc.appendChild(ballot);
	}

	/**
	 * Reads in the geometry of a ballot from a file
	 * @param path - the path to a xml file with the geometry
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown 
	 */
	public BallotGeometry(String path) throws SAXException, IOException {
		doc = Util.DomParse(path);
		
		Node node = doc.getElementsByTagName("ballot").item(0);
		this.width=Float.parseFloat(node.getAttributes().getNamedItem("width").getNodeValue());
		this.height=Float.parseFloat(node.getAttributes().getNamedItem("heigth").getNodeValue());
	}
	
	/**
	 * @return the size of the serial
	 */
	public int getNoDigitsInSerial() {
		return doc.getElementsByTagName("digit").getLength();
	}

	/** 
	 * @param digitId the number of the digit in the top serial
	 * @return a bounding rectangle for digit number "digit" in the serial number on the top page
	 */
	public Rectangle getSerialTop(String digitId) {
		Node node=getSerialTopNode(digitId);
		if (node==null)
			return null;
		return makeRectangle(node); 
	}

	/**  
	 * @param digitId the number of the digit in the top serial
	 * @return the xml node for the top digit in the serial number having id=digitId
	 */
	public Node getSerialTopNode(String digitId) {
		NodeList digits = doc.getElementsByTagName("digit");
		for (int i=0;i<digits.getLength();i++) {
			Node digit = digits.item(i);
			if (digit.getAttributes().getNamedItem("id").getNodeValue().compareTo(digitId)==0) {
				for (Node node = digit.getFirstChild();node!=null;node=node.getNextSibling()) {
					if (node.getNodeName().compareTo("top")==0) {
						return node;
					}
				}
			}
		}
		return null;
	}
	
	/** 
	 * @param digitId the number of the digit in the bottom serial
	 * @return a bounding rectangle for digit number "digit" in the serial number on the bottom page
	 */	
	public Rectangle getSerialBottom(String digitId) {
		Node node=getSerialBottomNode(digitId);
		if (node==null)
			return null;
		return makeRectangle(node); 
	}
	
	/**  
	 * @param digitId the number of the digit in the bottom serial
	 * @return the cluster for the bottom digit in the serial number having id=digitId
	 */
	public Cluster getSerialBottomCluster(String digitId) {
		Node node=getSerialBottomNode(digitId);
		if (node==null)
			return null;
		return (new Cluster(node)); 
	}

	/**
	 * @return the possitions of the serial digits on the bottom page
	 */
	public Vector<Cluster> getSerialBottomClusters() {
		Vector<Cluster> ret=new Vector<Cluster>();
		NodeList digits = doc.getElementsByTagName("digit");
		for (int i=0;i<digits.getLength();i++) {
			Node digit = digits.item(i);
			for (Node node = digit.getFirstChild();node!=null;node=node.getNextSibling()) {
				if (node.getNodeName().compareTo("bottom")==0) {
					ret.add(new Cluster(node));
				}
			}
		}
		return ret;
	}

	public Vector<Cluster> getSerialTopClusters() {
		Vector<Cluster> ret=new Vector<Cluster>();
		NodeList digits = doc.getElementsByTagName("digit");
		for (int i=0;i<digits.getLength();i++) {
			Node digit = digits.item(i);
			for (Node node = digit.getFirstChild();node!=null;node=node.getNextSibling()) {
				if (node.getNodeName().compareTo("top")==0) {
					ret.add(new Cluster(node));
				}
			}
		}
		return ret;
	}

	

	/**  
	 * @param digitId the number of the digit in the bottom serial
	 * @return the xml node for the bottom digit in the serial number having id=digitId
	 */
	public Node getSerialBottomNode(String digitId) {
		NodeList digits = doc.getElementsByTagName("digit");
		for (int i=0;i<digits.getLength();i++) {
			Node digit = digits.item(i);
			if (digit.getAttributes().getNamedItem("id").getNodeValue().compareTo(digitId)==0) {
				for (Node node = digit.getFirstChild();node!=null;node=node.getNextSibling()) {
					if (node.getNodeName().compareTo("bottom")==0) {
						return node;
					}
				}
			}
		}
		return null;
	}
	
	/** 
	 * @param race the race id
	 * @param candidate - the candidate id
	 * @return a bounding rectangle for the letter on the top page (rank 0) 
	 */
	public Rectangle getTop(String race, String candidate) {
		Node node=getTopNode(race, "0", candidate);
		if (node==null)
			return null;
		return makeRectangle(node);
	}

	/** 
	 * @param race the race id
	 * @param rank the rank (if a scantegrity ballot)
	 * @param candidate - the candidate id
	 * @return a bounding rectangle for the letter on the top page
	 */
	public Rectangle getTop(String race, String rank,String candidate) {
		Node node=getTopNode(race, rank, candidate);
		if (node==null)
			return null;
		return makeRectangle(node);
	}

	/** 
	 * @param race the race number
	 * @param rank 
	 * @param candidate
	 * @return a bounding rectangle for where the letter of the bottom page should appear
	 */
	public Rectangle getBottom(String race, String rank, String candidate) {
		Node node=getBottomNode(race, rank, candidate);
		if (node==null)
			return null;
		return makeRectangle(node);
	}

	/** 
	 * @param race
	 * @param rank
	 * @param candidate
	 * @return a cluster representing where the letter on bottom should apear 
	 */
	public Cluster getBottomCluster(String race, String rank, String candidate) {
		Node node=getBottomNode(race, rank, candidate);
		if (node==null)
			return null;
		return new Cluster(node);
	}

	public Cluster getTopCluster(String race, String rank, String candidate) {
		Node node=getTopNode(race, rank, candidate);
		if (node==null)
			return null;
		return new Cluster(node);
	}
	
	/** 
	 * @param race
	 * @param rank
	 * @param candidate
	 * @return an xml node from the geometry coresponding to the where the 
	 * bottom letter should appear (null if no such thing is found for the particular race, rank and candidate)  
	 */
	public Node getBottomNode(String race, String rank, String candidate) {
		NodeList digits = doc.getElementsByTagName("contest");
		for (int i=0;i<digits.getLength();i++) {
			Node digit = digits.item(i);
			if (digit.getAttributes().getNamedItem("id").getNodeValue().compareTo(race)==0) {
				for (Node node = digit.getFirstChild();node!=null;node=node.getNextSibling()) {
					if (node.getNodeName().compareTo("bottom")==0) {
						for (Node c = node.getFirstChild();c!=null;c=c.getNextSibling()) {
							if (c.getNodeName().compareTo("row")==0 && 
									c.getAttributes().getNamedItem("id").getNodeValue().compareTo(rank)==0) {
								for (Node cc = c.getFirstChild();cc!=null;cc=cc.getNextSibling()) {
									if (cc.getNodeName().compareTo("candidate")==0 && 
											cc.getAttributes().getNamedItem("id").getNodeValue().compareTo(candidate)==0) {
										return cc;							
									}
								}
							}
						}
					}
				}
			}
		}
		return null;
	}
	
	/**
	 * 
	 * @param race
	 * @param rank
	 * @param candidate
	 * @return an xml node from the geometry coresponding to the where the 
	 * top letter should appear (null if no such thing is found for the particular race, rank and candidate)  
	 */
	public Node getTopNode(String race, String rank, String candidate) {
		NodeList digits = doc.getElementsByTagName("contest");
		for (int i=0;i<digits.getLength();i++) {
			Node digit = digits.item(i);
			if (digit.getAttributes().getNamedItem("id").getNodeValue().compareTo(race)==0) {
				for (Node node = digit.getFirstChild();node!=null;node=node.getNextSibling()) {
					if (node.getNodeName().compareTo("top")==0) {
						for (Node c = node.getFirstChild();c!=null;c=c.getNextSibling()) {
							if (c.getNodeName().compareTo("row")==0 && 
									c.getAttributes().getNamedItem("id").getNodeValue().compareTo(rank)==0) {
									//c.getAttributes().getNamedItem("id").getNodeValue().compareTo(candidate)==0) {
								for (Node cc = c.getFirstChild();cc!=null;cc=cc.getNextSibling()) {
									if (cc.getNodeName().compareTo("candidate")==0 && 
											cc.getAttributes().getNamedItem("id").getNodeValue().compareTo(candidate)==0) {
											//cc.getAttributes().getNamedItem("id").getNodeValue().compareTo(rank)==0) {
										return cc;							
									}
								}
							}
						}
					}
				}
			}
		}
		return null;
	}

	/** 
	 * @return a vector of Clusters containing one element for every letter on
	 * the bottom page
	 */
	public Vector<Cluster> getContestBottomHoles() {
		Vector<Cluster> ret = new Vector<Cluster>();
		NodeList digits = doc.getElementsByTagName("contest");
		for (int i=0;i<digits.getLength();i++) {
			Node digit = digits.item(i);
			for (Node node = digit.getFirstChild();node!=null;node=node.getNextSibling()) {
				if (node.getNodeName().compareTo("bottom")==0) {
					for (Node c = node.getFirstChild();c!=null;c=c.getNextSibling()) {
						if (c.getNodeName().compareTo("row")==0){
							for (Node cc = c.getFirstChild();cc!=null;cc=cc.getNextSibling()) {
								if (cc.getNodeName().compareTo("candidate")==0) {
									ret.add(new Cluster(cc));							
								}
							}
						}
					}
				}
			}
		}
		return ret;
	}
	

	/**
	 * Adds a contest to the geometry
	 * @param qno - the question number
	 * @param top - where the top letter shold be
	 * @param bottom - where the bottom letters should be
	 * @throws Exception if bottom is not null (Scantegrity)
	 * then the number of letter on the bottom must be a multiple of
	 * the number of letters on the top. Otherwise an exception is thrown
	 */
	public void addContest(int qno, Vector<Cluster> top, Vector<Cluster> bottom) throws Exception {
		if (top == null || bottom == null) return;
		if (bottom.size() == 0 || top.size() == 0) return;
		if (bottom!=null && bottom.size() % top.size() !=0) {
			System.out.println(top);
			System.out.println(bottom);
			throw new Exception("on contest number "+qno+" bottom marks detected "+bottom.size()+" and top marks detected "+top.size());
		}
		
		int noRowsBottom=sortOnYThenOnX(bottom);
		int noColumnsTop=sortOnXThenOnY(top);

//System.out.println("line number: "+Thread.currentThread().getStackTrace()[2].getLineNumber()+" "+noRowsBottom+" "+noColumnsTop);
//System.out.println("Bottom "+bottom);
//System.out.println("Top "+top);

		Node contests = null;
		NodeList allPrevious=doc.getElementsByTagName("contests");
		//delete any previous element
		if (allPrevious.item(0)==null) {
			contests = doc.createElement("contests");
			ballot.appendChild(contests);
		} else {
			contests = allPrevious.item(0);
		}
		
		Element contest = doc.createElement("contest");
		contest.setAttribute("id", qno+"");
		contests.appendChild(contest);
		
//System.out.println("NoColumnsTop="+noColumnsTop+" topSize="+top.size());		
//System.out.println(top.size()/noColumnsTop+" "+top);		
		Element t = makeContest(top, top.size()/noColumnsTop, "top");
		contest.appendChild(t);

		if (bottom!=null) {
			Element b = makeContest(bottom, bottom.size()/noRowsBottom, "bottom");
			contest.appendChild(b);
		}
	}

	protected Element makeContest(Vector<Cluster> bottom,int rowSize,String name) {
		Element b = doc.createElement(name);
		if (bottom!=null) {
			Element row=null;
			for (int i=0;i<bottom.size();i++) {
				if (i%rowSize==0) {
					row=doc.createElement("row");
					row.setAttribute("id", i/rowSize+"");
					b.appendChild(row);
				}
				Cluster c=bottom.get(i);
				c.setName("candidate");
				Element e=c.getNodeXYFromTo(doc);
				e.setAttribute("id", (i%rowSize)+"");
				row.appendChild(e);			
			}
		}
		return b;
	}
	
	/**
	 * Adds the where the serial number should be
	 * @param top - the serial number on the top page
	 * @param bottom - the serial number on the bottom page
	 */
	public void setSerial(Vector<Cluster> top, Vector<Cluster> bottom) {
		if (bottom!=null && bottom.size()!=top.size()) {
			System.out.println(top);
			System.out.println(bottom);
			return;
			//throw new Exception("on contest number "+qno+" bottom marks detected "+bottomOrange.size()+" and top marks detected "+topOrange.size());
		}

		BallotGeometry.sortOnX(top,0,top.size()-1);
		if (bottom!=null) {
			BallotGeometry.sortOnX(bottom,0,bottom.size()-1);
			
			Cluster hole=bottom.firstElement();
			holeDiameter=(hole.getXmax()-hole.getXmin());			
		} else {
			//Cluster hole=top.firstElement();
			holeDiameter=0;//(hole.getXmax()-hole.getXmin());			
		}
		
		Element ballot=(Element)doc.getElementsByTagName("ballot").item(0);
		ballot.setAttribute("holeDiameter",String.format("%.3f",holeDiameter));		

		NodeList allPrevious=doc.getElementsByTagName("serial");
		//delete any previous element
		if (allPrevious.item(0)!=null) {
			for (int i=0;i<allPrevious.getLength();i++) {
				doc.removeChild(allPrevious.item(i));
			}
		}
		Node node = doc.createElement("serial");
		Cluster c;
		for (int i=0;i<top.size();i++) {
			Element digit = doc.createElement("digit");
			digit.setAttribute("id",i+"");			
			digit.setAttribute("type","counter");

			c=top.get(i); 
			c.setName("top");
			digit.appendChild(c.getNodeXYFromTo(doc));
			
			if (bottom!=null) {
				c=bottom.get(i); 
				c.setName("bottom");
				digit.appendChild(c.getNodeXYFromTo(doc));
			}
			
			node.appendChild(digit);
		}
		ballot.appendChild(node);		
	}

	/**
	 * @param alignment the alignment mark to be added
	 */
	public void addAlignment(Cluster alignment) {
		Node alignments = null;
		NodeList allPrevious=doc.getElementsByTagName("alignments");
		if (allPrevious.item(0)==null) {
			alignments = doc.createElement("alignments");
			ballot.appendChild(alignments);
		} else {
			alignments = allPrevious.item(0);
		}
		
		alignment.setName("alignment");
		alignments.appendChild(alignment.getNodeXY(doc));
	}

	/** 
	 * @param holeOnly the place where a hole shoold be drilled (in addition to letters and serial number)
	 */
	public void addHoleOnly(Cluster holeOnly) {
		Node alignments = null;
		NodeList allPrevious=doc.getElementsByTagName("holesOnly");
		if (allPrevious.item(0)==null) {
			alignments = doc.createElement("holesOnly");
			ballot.appendChild(alignments);
		} else {
			alignments = allPrevious.item(0);
		}
		
		holeOnly.setName("holeOnly");
		alignments.appendChild(holeOnly.getNodeXY(doc));
	}
	

	/**
	 * Sorts a vector of clusters based on their X coordinates (horizontaly) 
	 * @param q - the vecotr to be sorted (it is modified by this method)
	 * @param start - the start possition (including)
	 * @param stop - the stop possition (exclusive)
	 */
	public static void sortOnX(Vector<Cluster> q,int start,int stop) {
		boolean sort = false;
		if (q.size() < 1)
			return;
		
		//sort on Y
		while (! sort) {
			sort = true;
			for (int i=start;i<stop-1;i++) {
				if (q.get(i).getCenterOfMass().x > q.get(i+1).getCenterOfMass().x) {
					Cluster temp = q.get(i);
					q.setElementAt(q.get(i+1),i);
					q.setElementAt(temp,i+1);
					sort = false;
				}
			}
		}
	}
	
	/**
	 * Sorts a vector of clusters based on their Y coordinates (vertically) 
	 * @param q - the vecotr to be sorted (it is modified by this method)
	 * @param start - the start possition (including)
	 * @param stop - the stop possition (exclusive)
	 */
	public static void sortOnY(Vector<Cluster> q,int start,int stop) {
		boolean sort = false;
		if (q.size() < 1)
			return;
		
		//sort on Y
		while (! sort) {
			sort = true;
			for (int i=start;i<stop-1;i++) {
				if (q.get(i).getCenterOfMass().y > q.get(i+1).getCenterOfMass().y) {
					Cluster temp = q.get(i);
					q.setElementAt(q.get(i+1),i);
					q.setElementAt(temp,i+1);
					sort = false;
				}
			}
		}
	}

	/**
	 * Sorts a vector on cluster on X (horizontally). It then finds the
	 * ones that have a very close X and for evry such grup, it sorts
	 * them on Y
	 * @param q - the vector to be sorted (it is modified by this method)
	 * @return - the number of groups with simmilar X coordinates
	 */
	public static int sortOnXThenOnY(Vector<Cluster> q) {
		if (q.size() == 0) return 0;
		sortOnX(q, 0, q.size());
//System.out.println(q);		
		//go through the sorted clusters and you should see m clusters on the same x
		int noRows=getNoRowsFromVectorSortedOnX(q);
//System.out.println("[BallotGeometry Line 559]NoRows="+noRows);		
		int noColumns=q.size()/noRows;
		
		//sort each row
		for (int i=0;i<noColumns;i++)
			sortOnY(q, i*noRows, (i+1)*noRows);
		return noColumns;
	}

	/**
	 * Sorts a vector on cluster on Y (vertically). It then finds the
	 * ones that have a very close Y and for evry such grup, it sorts
	 * them on X
	 * @param q - the vector to be sorted (it is modified by this method)
	 * @return - the number of groups with simmilar Y coordinates
	 */
	public static int sortOnYThenOnX(Vector<Cluster> q) {
		if (q==null)
			return 0;
		
		sortOnY(q, 0, q.size());
		
		//go through the sorted clusters and you should see m clusters on the same x
		int noColumns=getNoColumnsFormVectorSortedOnY(q);	
		int noRows=q.size()/noColumns;
		
		//sort each row
		for (int i=0;i<noRows;i++)
			sortOnY(q, i*noColumns, (i+1)*noColumns);
		return noRows;
	}
	
	/** 
	 * @param q - a vector of Clusters already sorted on X (does not get modified by this method)
	 * @return - the number of groups with similar
	 * X coordinates
	 */
	public static int getNoRowsFromVectorSortedOnX(Vector<Cluster> q) {		
		if (q==null || q.size()==0) 
			return 0;
		if (q.size()==1)
			return 1;
		
		double diffx=Math.abs(q.get(0).getCenterOfMass().x - q.get(1).getCenterOfMass().x);

		double currentDiffx;
		for (int i=1;i<q.size()-1;i++) {
			currentDiffx=Math.abs(q.get(i+1).getCenterOfMass().x - q.get(i).getCenterOfMass().x);
			if (currentDiffx>7*diffx)
				return i+1;
		}

		return q.size();
/*		
		double diffy=Math.abs(q.get(0).getCenterOfMass().y - q.get(1).getCenterOfMass().y);	
		if (diffy<0.1)
			return q.size();
		double currentDiffy;

		for (int i=1;i<q.size()-1;i++) {
			currentDiffy=(q.get(i+1).getCenterOfMass().y - q.get(i).getCenterOfMass().y);
			if (currentDiffy<-0.1)
				return i+1;			
		}
		return q.size();
*/		
	}

	/** 
	 * @param q - a vector of Clusters already sorted on Y (does not get modified by this method)
	 * @return - the number of groups with similar
	 * Y coordinates
	 */
	public static int getNoColumnsFormVectorSortedOnY(Vector<Cluster> q) {
		if (q==null)
			return 0;
		if (q.size()==1)
			return 1;		
		double diffy=Math.abs(q.get(0).getCenterOfMass().y - q.get(1).getCenterOfMass().y);
		double currentDiffy;
		for (int i=1;i<q.size()-1;i++) {
			currentDiffy=Math.abs(q.get(i).getCenterOfMass().y - q.get(i+1).getCenterOfMass().y);
			if (currentDiffy!=0 && diffy/currentDiffy<0.5) {
				return i+1;
			}
		}
		return q.size();
	}
	
	/**
	 * Writes the geometry
	 * @param fos - the output stream to write to
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown
	 */
	public void write(OutputStream fos) throws IOException {
		OutputFormat of = new OutputFormat("XML","ISO-8859-1",false);
		of.setIndent(1);
		of.setIndenting(true);
		XMLSerializer serializer = new XMLSerializer(fos,of);
		serializer.asDOMSerializer();
		serializer.serialize( doc.getDocumentElement() );		
	}
	
	/**
	 * @return a bouding rectangle where the "Finish voting" button should be on the top part of the form form.
	 * It is places horizontally in the middle of the page, 0.5 inches to the top.
	 * It has a height of 0.4 inches
	 */
	public Rectangle getUpperFinishButton() {
		double y=0.5;//getUpperAlignment().getY();
		return new Rectangle((width/2-1)*72,(float)((height-y-0.2)*72),(width/2+1)*72,(float)((height-y+0.2)*72));
	}

	/**
	 * @return a bouding rectangle where the "Finish voting" button should be on the bottom part of the form.
	 * It is places horizontally in the middle of the page, 0.5 inches to the bottom.
	 * It has a height of 0.4 inches
	 */
	public Rectangle getLowerFinishButton() {
		double y=height-0.5;//getLowerAlignment().getY();
		return new Rectangle((width/2-1)*72,(float)((height-y-0.2)*72),(width/2+1)*72,(float)((height-y+0.2)*72));
	}

	public Rectangle getInstructionButton() {
		double y=height-0.5;//getLowerAlignment().getY();
		return new Rectangle((width/2-2f)*72,(float)((height-y-0.2)*72),(width/2-1.1f)*72,(float)((height-y+0.2)*72));
	}

	public Rectangle getHideTop() {
		double y=height-0.5;//getLowerAlignment().getY();
		return new Rectangle((width/2+1.1f)*72,(float)((height-y-0.2)*72),(width/2+1.9f)*72,(float)((height-y+0.2)*72));
	}

	public Rectangle getHideBottom() {
		double y=height-0.5;//getLowerAlignment().getY();
		return new Rectangle((width/2+2)*72,(float)((height-y-0.2)*72),(width/2+3)*72,(float)((height-y+0.2)*72));
	}

	public Rectangle getShowBoth() {
		double y=height-0.5;//getLowerAlignment().getY();
		return new Rectangle((width/2+3.1f)*72,(float)((height-y-0.2)*72),(width/2+4)*72,(float)((height-y+0.2)*72));
	}

	/** 
	 * @param node
	 * @return a Rectangle surounding the cluster in pdf coordinates
	 */
	public Rectangle makeRectangle(Node node) {
		NamedNodeMap attr = node.getAttributes();
		float fromx = Float.parseFloat(attr.getNamedItem("fromx").getNodeValue())*72;
		float fromy = (height-Float.parseFloat(attr.getNamedItem("fromy").getNodeValue()))*72;
		float tox = Float.parseFloat(attr.getNamedItem("tox").getNodeValue())*72;
		float toy = (height-Float.parseFloat(attr.getNamedItem("toy").getNodeValue()))*72;
		//return new Rectangle(fromx,fromy,tox,toy);		
		return new Rectangle(fromx,toy,tox,fromy);
	}
	
	/** 
	 * @param p
	 * @return a Rectangle surounding the point in pdf coordinates. The 
	 * width and the height of the rectangle are 0.25inches each
	 */
	public Rectangle makeRectangle(Point2D.Double p) {
		float fromx = (float)(p.getX()-0.125)*72;
		float fromy = (float)(height-p.getY()-0.125)*72;
		float tox = (float)(p.getX()+0.125)*72;;
		float toy = (float)(height-p.getY()+0.125)*72;;
		return new Rectangle(fromx,fromy,tox,toy);		
	}
	
	
	public float getHeight() {
		return height;
	}

	public float getWidth() {
		return width;
	}
	
	public float getHoleDiameter() {
		Node node = doc.getElementsByTagName("ballot").item(0);
		
		if (node.getAttributes().getNamedItem("holeDiameter")==null) return 0;
		
		return Float.parseFloat(node.getAttributes().getNamedItem("holeDiameter").getNodeValue());		
	}

	public void setHoleDiameter(double diameter) {
		Element node =(Element)doc.getElementsByTagName("ballot").item(0);
		node.setAttribute("holeDiameter",diameter+"");		
	}	
	
	/** 
	 * @return the alignment mark with the smallest Y
	 */
	public Point2D.Double getUpperAlignment() {
		NodeList alignments = doc.getElementsByTagName("alignment");
		TreeMap<Double,Double> ret=new TreeMap<Double, Double>(); 
		for (int i=0;i<alignments.getLength();i++) {
			Node alignment = alignments.item(i);
			double x=Double.parseDouble(alignment.getAttributes().getNamedItem("x").getNodeValue());
			double y=Double.parseDouble(alignment.getAttributes().getNamedItem("y").getNodeValue());
			ret.put(y,x);
		}
		double y=ret.firstKey();
		double x=ret.get(y);
		return new Point2D.Double(x,y);
	}
	
	/**
	 * @return the alignment mark with the greatest Y
	 */
	public Point2D.Double getLowerAlignment() {
		NodeList alignments = doc.getElementsByTagName("alignment");
		TreeMap<Double,Double> ret=new TreeMap<Double, Double>(); 
		for (int i=0;i<alignments.getLength();i++) {
			Node alignment = alignments.item(i);
			double x=Double.parseDouble(alignment.getAttributes().getNamedItem("x").getNodeValue());
			double y=Double.parseDouble(alignment.getAttributes().getNamedItem("y").getNodeValue());
			ret.put(y,x);
		}
		double y=ret.lastKey();
		double x=ret.get(y);
		return new Point2D.Double(x,y);
	}

	/** 
	 * @return a default election speficicartion. The questions are of rank type
	 * if the number of letters on the top is different to the number of letters on the bottom.
	 * All candidates can be ranked by default.
	 * 
	 * Otherwise, the question is a choose one out of n.
	 */
	public ElectionSpecification getDefaultElectionSpec() {
		Hashtable<String,Section> sections=new Hashtable<String, Section>();
		//by defauld there is only one section
		Section section=new Section();
		section.setId(0+"");
		section.setPossition(1);
		Hashtable<String, Question> questions = new Hashtable<String, Question>();
		int noq = doc.getElementsByTagName("contest").getLength();
		for (int q=0;q<noq;q++) {
			Question question=new Question();
			question.setId(q+"");
			question.setPossition(q+1);
			int nor=0;;
			while (getBottomNode(q+"",nor+"", "0")!=null) {
				nor++;
			}
			if (nor>1)
				question.setTypeOfAnswer(Constants.RANK);
			else {
				while (getTopNode(q+"",nor+"", "0")!=null) {
					nor++;
				}
				if (nor>1)
					question.setTypeOfAnswer(Constants.RANK);
				else
					question.setTypeOfAnswer(Constants.ONE_ANSWER);
			}
			question.setMax(nor);
			Hashtable<String, Answer> answers=new Hashtable<String, Answer>();
			int cno=0;
			while (getTopNode(q+"","0", cno+"")!=null) {
				Answer answer=new Answer();
				answer.setId(cno+"");
				answer.setPossition(cno+1);
				answers.put(answer.getId(), answer);
				cno++;
			}
			question.setAnswers(answers);
			questions.put(question.getId(), question);
		}
		section.setQuestions(questions);
		sections.put(section.getId(), section);
		
		return new ElectionSpecification("TakomaPark3Nov2009",sections);
	}

	public String getDefaultPartitions() {
		StringBuffer sb=new StringBuffer();
		
		sb.append("<electionSpecification version=\"0.1\">\n");
		sb.append("\t<electionInfo id=\"TakomaPark3Nov2009\">\n");
		sb.append("\t\t<sections>\n");
		sb.append("\t\t\t<section id=\"0\">\n");
		sb.append("\t\t\t\t<questions>\n");

		
		int noq = doc.getElementsByTagName("contest").getLength();
		for (int q=0;q<noq;q++) {
			sb.append("\t\t\t\t<question id=\""+q+"\" partitionNo=\""+q+"\"/>\n");
		}
		
		sb.append("\t\t\t\t</questions>\n");
		sb.append("\t\t\t</section>\n");
		sb.append("\t\t</sections>\n");
		sb.append("\t</electionInfo>\n");
		sb.append("</electionSpecification>\n");

		return sb.toString();
	}

	
	/** 
	 * @return the number of contests present on the ballot
	 */
	public int getNoRaces() {
		return doc.getElementsByTagName("contest").getLength();
	}
	

	/** 
	 * @param serialBarcode where the serial number in barcode is placed
	 */
	public void setSerialBarcode(Cluster serialBarcode) {
		serialBarcode.setName("barcode");
		Node serialNode=ballot.getElementsByTagName("serial").item(0);
		serialNode.appendChild(serialBarcode.getNodeXYFromTo(doc));
	}

	/** 
	 * @param serialBulleted where the serial number in bullets readable by a mark sense machine is placed
	 */
	public void setSerialBulleted(Cluster serialBulleted) {
		serialBulleted.setName("bulleted");
		Node serialNode=ballot.getElementsByTagName("serial").item(0);
		serialNode.appendChild(serialBulleted.getNodeXYFromTo(doc));		
	}

	/** 
	 * @return where the serial number in barcode is placed
	 */
	public Rectangle getSerialBarcode() {
		Node node=getSerialBarcodeNode();
		if (node==null)
			return null;
		return makeRectangle(node);
	}

	/** 
	 * @return where the serial number in bullets readable by a mark sense machine is placed
	 */
	public Node getSerialBarcodeNode() {
		return doc.getElementsByTagName("barcode").item(0);
	}

	/**
	 * Equally divided the rectangle where the serial number should be 
	 * @return an array of rectables, with 10 columns and as many rows as in the
	 * serial number
	 */
	public Rectangle[][] getSerialBulleted() {
		Node node=getSerialBulletedNode();
		if (node==null)
			return null;
		Rectangle rect=makeRectangle(node);
		
		int noRows=getNoDigitsInSerial();
		int noColumns=10;
		
		Rectangle[][] ret=new Rectangle[noRows][noColumns];
		
		float cellWidth=Math.abs(rect.getWidth())/noColumns;
		float cellHeight=Math.abs(rect.getHeight())/noRows;
		
		float zerox=Math.min(rect.getLeft(),rect.getRight());
		float zeroy=Math.max(rect.getTop(),rect.getBottom());		

		float fromx = 0;
		float fromy = 0;
		float tox = 0;
		float toy = 0;

		for (int rowNo=0;rowNo<noRows;rowNo++) {
			//fromy
			toy=zeroy-rowNo*cellHeight;
			//toy
			fromy=zeroy-(rowNo+1)*cellHeight-1;
			for (int  columnNo=0;columnNo<noColumns;columnNo++) {
				fromx=zerox+columnNo*cellWidth;
				tox=zerox+(columnNo+1)*cellWidth-1;		
				ret[rowNo][columnNo]=new Rectangle(fromx,fromy,tox,toy);
			}
		}
		return ret;

	}

	/**
	 * @return the xml node coresponding to where the serial number bulleted should be
	 */
	public Node getSerialBulletedNode() {
		return doc.getElementsByTagName("bulleted").item(0);
	}

	public double getDonutThicknessBottom() {
		return getHoleDiameter()*0.25;
	}

	public double getDonutThicknessTop() {
		return getHoleDiameter()*0.25;
	}
}