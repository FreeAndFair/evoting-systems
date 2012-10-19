package org.scantegrity.common;

import java.io.Serializable;

import org.bouncycastle.util.encoders.Base64;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.xml.sax.Attributes;

/**
 * A row in the P table of the punchboard
 * @author stefan
 *
 */

public class Prow implements Serializable {

	private static final long serialVersionUID = 3209313325585641044L;
	
	int id=-1;
	byte[] vote=null;
	byte[] page1=null;
	byte[] page2=null;
	byte[] s1=null;
	byte[] s2=null;
	byte[] c1=null;
	byte[] c2=null;
	ChosenPage chosenPage=ChosenPage.BOTH;
	
	static Operation operation=Operation.NONE;
	
	public static final String idAttr="id";
	public static final String voteAttr="p3";
	public static final String page1Attr="p1";
	public static final String page2Attr="p2";
	public static final String s1Attr="s1";
	public static final String s2Attr="s2";
	public static final String c1Attr="c1";
	public static final String c2Attr="c2";
	public static final String choosePageAttr="page";
	public static enum ChosenPage {TOP,BOTTOM,NONE,BOTH};
	
	public static enum Operation {OPEN_COMMITMENTS, PUBLISH_COMMITMENTS, NONE};
	
	/**
	 * empty constructor
	 */	
	public Prow() {
		
	}

	/** 
	 * @param row a DOM node contaning a P row 
	 * @throws Exception
	 */
	public Prow(Node row) throws Exception {
		setUp(row);
	}
	
	/** 
	 * @param attrs a SAX set of attributes contaning a P row
	 * @throws Exception
	 */
	public Prow(Attributes attrs) throws Exception {
		setUp(attrs);
	}
	
	protected void setUp(Attributes attrs) throws Exception {
		for (int i = 0; i < attrs.getLength(); i++) {
            String aName = attrs.getLocalName(i);
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
				chosenPage=ChosenPage.valueOf(attrs.getValue(i));
		}
		
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
			chosenPage=ChosenPage.valueOf(attr.getNodeValue());
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

	public ChosenPage getChosenPage() {
		return chosenPage;
	}

	public void setChosenPage(ChosenPage chosenPage) {
		this.chosenPage = chosenPage;
	}

	public int getId() {
		return id;
	}

	public void setId(int id) {
		this.id = id;
	}

	public byte[] getVote() {
		return vote;
	}

	public void setVote(byte[] vote) {
		this.vote = vote;
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

	public static Operation getOperation() {
		return operation;
	}

	/** 
	 * @param operation the operation that all the P rows will have
	 */
	public static void setOperation(Operation operation) {
		Prow.operation = operation;
	}
	
	/**
	 * creates an xml representation of the P row.
	 * It takes into consideration if it should publish or open the commitments,
	 * on which side and if it should publish votes (p3) or not
	 */	
	public String toString() {
		StringBuffer ret=new StringBuffer("");

		ret.append("\t\t\t<row id=\""+getId()+"\"");
		if (page1!=null && operation.equals(Prow.Operation.OPEN_COMMITMENTS)) {
			ret.append(" "+Prow.page1Attr+"=\""+Util.toString(page1)+"\"");
		}
		if (s1!=null && operation.equals(Prow.Operation.OPEN_COMMITMENTS)) {
			ret.append(" "+Prow.s1Attr+"=\""+new String(Base64.encode(s1))+"\"");
		}
		if (c1!=null && operation.equals(Prow.Operation.PUBLISH_COMMITMENTS)) {
			ret.append(" "+Prow.c1Attr+"=\""+new String(Base64.encode(c1))+"\"");
		}
		if (page2!=null && operation.equals(Prow.Operation.OPEN_COMMITMENTS)) {
			ret.append(" "+Prow.page2Attr+"=\""+Util.toString(page2)+"\"");
		}
		if (s2!=null && operation.equals(Prow.Operation.OPEN_COMMITMENTS)) {
			ret.append(" "+Prow.s2Attr+"=\""+new String(Base64.encode(s2))+"\"");
		}
		if (c2!=null && operation.equals(Prow.Operation.PUBLISH_COMMITMENTS)) {
			ret.append(" "+Prow.c2Attr+"=\""+new String(Base64.encode(c2))+"\"");
		}
		
		if (vote!=null && operation.equals(Prow.Operation.NONE)) {
			ret.append(" "+Prow.voteAttr+"=\""+Util.toString(vote)+"\"");
		}
		
		if (operation.equals(Prow.Operation.NONE)) {
			ret.append(" "+Prow.choosePageAttr+"=\""+chosenPage+"\"");
		}
		
		ret.append("/>\n");
		return ret.toString();
	}
}
