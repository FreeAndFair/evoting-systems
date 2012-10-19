package org.scantegrity.common;

import java.io.Serializable;

import org.bouncycastle.util.encoders.Base64;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.xml.sax.Attributes;

/**
 * A row in the D table of the punchboard
 * @author stefan
 *
 */
public class Drow implements Serializable {

	private static final long serialVersionUID = 344436062219106525L;
	
	int id=-1;
	byte[] vote=null;
	byte[] page1=null;
	byte[] page2=null;
	byte[] s1=null;
	byte[] s2=null;
	byte[] c1=null;
	byte[] c2=null;
	ChosenSide chosenPage=ChosenSide.NONE;
	static Operation operation=Operation.NONE;
	int pid=-1;
	int rid=-1;
	
	public static final String idAttr="id";
	public static final String voteAttr="d3";
	public static final String page1Attr="d2";
	public static final String page2Attr="d4";
	public static final String s1Attr="sl";
	public static final String s2Attr="sr";
	public static final String c1Attr="cl";
	public static final String c2Attr="cr";
	public static final String choosePageAttr="side";
	public static enum ChosenSide {LEFT,RIGHT,NONE,BOTH};
	public static final String pidAttr="pid";
	public static final String ridAttr="rid";	
	
	public static enum Operation {OPEN_COMMITMENTS, PUBLISH_COMMITMENTS, PUBLISH_RESULTS, NONE};
	
	/**
	 * empty constructor
	 */
	public Drow() {
		
	}
	
	/** 
	 * @param row a DOM node contaning a D row 
	 * @throws Exception
	 */
	public Drow(Node row) throws Exception {
		setUp(row);
	}
	
	/** 
	 * @param attrs a SAX set of attributes contaning a D row
	 * @throws Exception
	 */
	public Drow(Attributes attrs) throws Exception {
		setUp(attrs);
	}
	
	protected void setUp(Node row) throws Exception {
		NamedNodeMap attrs = row.getAttributes();
		Node attr=null;
		
		attr=attrs.getNamedItem(idAttr);
		id=Integer.parseInt(attr.getNodeValue());

		attr=attrs.getNamedItem(voteAttr);
		if (attr!=null)
			vote=Util.parse(attr.getNodeValue());
		
		attr=attrs.getNamedItem(page1Attr);
		if (attr!=null)
			page1=Util.parse(attr.getNodeValue());

		attr=attrs.getNamedItem(page2Attr);
		if (attr!=null)
			page2=Util.parse(attr.getNodeValue());		
		
		attr=attrs.getNamedItem(s1Attr);
		if (attr!=null)
			s1=Base64.decode(attr.getNodeValue());
		
		attr=attrs.getNamedItem(s2Attr);
		if (attr!=null)
			s2=Base64.decode(attr.getNodeValue());
		
		attr=attrs.getNamedItem(c1Attr);
		if (attr!=null)
			c1=Base64.decode(attr.getNodeValue());
		
		attr=attrs.getNamedItem(c2Attr);
		if (attr!=null)
			c2=Base64.decode(attr.getNodeValue());
		
		attr=attrs.getNamedItem(choosePageAttr);
		if (attr!=null)
			chosenPage=ChosenSide.valueOf(attr.getNodeValue());
		
		attr=attrs.getNamedItem(pidAttr);
		if (attr!=null)
			pid=Integer.parseInt(attr.getNodeValue());
		
		attr=attrs.getNamedItem(ridAttr);
		if (attr!=null)
			rid=Integer.parseInt(attr.getNodeValue());
	}
	
	protected void setUp(Attributes attrs) throws Exception {
		for (int i = 0; i < attrs.getLength(); i++) {
            String aName = attrs.getLocalName(i); // Attr name 
            if ("".equals(aName)) aName = attrs.getQName(i);
            
			if (aName.equals(idAttr))
				id = Integer.parseInt(attrs.getValue(i));
			else
			if (aName.equals(voteAttr))
				vote=Util.parse(attrs.getValue(i));
			else
			if (aName.equals(page1Attr))
				page1 = Util.parse(attrs.getValue(i));
			else
			if (aName.equals(page2Attr))
				page2 = Util.parse(attrs.getValue(i));
			else
			if (aName.equals(c1Attr))
				c1=Base64.decode(attrs.getValue(i));
			else
			if (aName.equals(c1Attr))
				c2=Base64.decode(attrs.getValue(i));
			else
			if (aName.equals(s1Attr))
				s1=Base64.decode(attrs.getValue(i));
			else
			if (aName.equals(s2Attr))
				s2=Base64.decode(attrs.getValue(i));
			else
			if (aName.equals(choosePageAttr))
				chosenPage=ChosenSide.valueOf(attrs.getValue(i));
			else
			if (aName.equals(pidAttr))
				pid = Integer.parseInt(attrs.getValue(i));
			else
			if (aName.equals(ridAttr))
				rid = Integer.parseInt(attrs.getValue(i));
		}
	}

	public int getPid() {
		return pid;
	}

	public void setPid(int pid) {
		this.pid = pid;
	}

	public int getRid() {
		return rid;
	}

	public void setRid(int rid) {
		this.rid = rid;
	}

	public byte[] getC1() {
		return c1;
	}

	public void setC1(byte[] c1) {
		this.c1 = c1;
	}

	public byte[] getC2() {
		return c2;
	}

	public void setC2(byte[] c2) {
		this.c2 = c2;
	}

	public ChosenSide getChosenSide() {
		return chosenPage;
	}

	public void setChosenSide(ChosenSide chosenPage) {
		this.chosenPage = chosenPage;
	}

	public int getId() {
		return id;
	}

	public void setId(int id) {
		this.id = id;
	}

	public byte[] getPage1() {
		return page1;
	}

	public void setPage1(byte[] page1) {
		this.page1 = page1;
	}

	public byte[] getPage2() {
		return page2;
	}

	public void setPage2(byte[] page2) {
		this.page2 = page2;
	}

	public byte[] getS1() {
		return s1;
	}

	public void setS1(byte[] s1) {
		this.s1 = s1;
	}

	public byte[] getS2() {
		return s2;
	}

	public void setS2(byte[] s2) {
		this.s2 = s2;
	}

	public byte[] getVote() {
		return vote;
	}

	public void setVote(byte[] vote) {
		this.vote = vote;
	}

	public static Operation getOperation() {
		return operation;
	}

	/** 
	 * @param operation the opperation performed on all the rows of all D tables
	 */
	public static void setOperation(Operation operation) {
		Drow.operation = operation;
	}
	
	/**
	 * creates an xml representation of the D row.
	 * It takes into consideration if it should publish or open the commitments,
	 * on which side and if it should publish results (d3) or not
	 */
	public String toString() {
		StringBuffer ret=new StringBuffer("");

		ret.append("\t\t\t\t\t<row id=\""+getId()+"\"");
		if (operation.equals(Drow.Operation.OPEN_COMMITMENTS)
				&& (chosenPage.equals(ChosenSide.LEFT)
						|| chosenPage.equals(ChosenSide.BOTH)
						)
				) {
			ret.append(" "+Drow.pidAttr+"=\""+pid+"\"");
			ret.append(" "+Drow.page1Attr+"=\""+Util.toString(page1)+"\"");
			ret.append(" "+Drow.s1Attr+"=\""+new String(Base64.encode(s1))+"\"");
		}
		if (operation.equals(Drow.Operation.PUBLISH_COMMITMENTS)
				&& (chosenPage.equals(ChosenSide.LEFT)
						|| chosenPage.equals(ChosenSide.BOTH)
						)
				) {				
			ret.append(" "+Drow.c1Attr+"=\""+new String(Base64.encode(c1))+"\"");
		}
		if (operation.equals(Drow.Operation.PUBLISH_RESULTS)) {
			ret.append(" "+Drow.voteAttr+"=\""+Util.toString(vote)+"\"");
		}
		if (operation.equals(Drow.Operation.OPEN_COMMITMENTS)
				&& (chosenPage.equals(ChosenSide.RIGHT)
						|| chosenPage.equals(ChosenSide.BOTH)
						)
				) {
			ret.append(" "+Drow.ridAttr+"=\""+rid+"\"");
			ret.append(" "+Drow.page2Attr+"=\""+Util.toString(page2)+"\"");
			ret.append(" "+Drow.s2Attr+"=\""+new String(Base64.encode(s2))+"\"");
		}
		if (c2!=null && operation.equals(Drow.Operation.PUBLISH_COMMITMENTS)) {
			ret.append(" "+Drow.c2Attr+"=\""+new String(Base64.encode(c2))+"\"");
		}
		/*
		if (chosenPage.equals(ChosenSide.LEFT) || chosenPage.equals(ChosenSide.RIGHT)) {
			ret.append(" "+Drow.choosePageAttr+"=\""+chosenPage+"\"");
		}
		*/
		ret.append("/>\n");
		return ret.toString();
	}
}
