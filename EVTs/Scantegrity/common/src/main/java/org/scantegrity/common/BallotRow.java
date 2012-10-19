package org.scantegrity.common;

import java.io.Serializable;

import org.bouncycastle.util.encoders.Base64;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.xml.sax.Attributes;

public class BallotRow implements Serializable {

	private static final long serialVersionUID = 6773002108719739034L;
	
	public static final String pidAttr="pid";
	
	public static final String barcodeSerialAttr="barcodeSerial";
	public static final String barcodeSerialCommitmentAttr="barcodeSerialCommitment";
	public static final String barcodeSerialSaltAttr="barcodeSerialSalt";
	
	public static final String webSerialAttr="webSerial";
	public static final String webSerialCommitmentAttr="webSerialCommitment";
	public static final String webSerialSaltAttr="webSerialSalt";
	
	public static final String stubSerialAttr="stubSerial";
	public static final String stubSerialCommitmentAttr="stubSerialCommitment";
	public static final String stubSerialSaltAttr="stubSerialSalt";
	
	//public static final String password2Attr="password2";
	//public static final String password2CommitmentAttr="password2Commitment";
	//public static final String password2SaltAttr="password2Salt";
	
	
	int pid=-1;
	
	String barcodeSerial=null;
	byte[] barcodeSerialCommitment=null;
	byte[] barcodeSerialSalt=null;
	
	String webSerial=null;
	byte[] webSerialCommitment=null;
	byte[] webSerialSalt=null;
	
	String stubSerial=null;
	byte[] stubSerialCommitment=null;
	byte[] stubSerialSalt=null;
	
	/*
	String password2=null;
	byte[] password2Commitment=null;
	byte[] password2Salt=null;
	*/

	public BallotRow() {
		
	}
	
	public BallotRow(Node node) throws Exception {
		setUp(node);
	}
	
	public BallotRow(Attributes attrs) throws Exception {
		setUp(attrs);
	}
	
	protected void setUp(Node row) throws Exception {
		NamedNodeMap attrs = row.getAttributes();
		Node attr=null;

		attr=attrs.getNamedItem(pidAttr);
		if (attr!=null)
			pid=Integer.parseInt(attr.getNodeValue());
		
		attr=attrs.getNamedItem(barcodeSerialAttr);
		if (attr!=null)
			barcodeSerial=attr.getNodeValue();

		attr=attrs.getNamedItem(barcodeSerialCommitmentAttr);
		if (attr!=null)
			barcodeSerialCommitment=Base64.decode(attr.getNodeValue());
		
		attr=attrs.getNamedItem(barcodeSerialSaltAttr);
		if (attr!=null)
			barcodeSerialSalt=Base64.decode(attr.getNodeValue());

		
		attr=attrs.getNamedItem(webSerialAttr);
		if (attr!=null)
			webSerial=attr.getNodeValue();
		
		attr=attrs.getNamedItem(webSerialCommitmentAttr);
		if (attr!=null)
			webSerialCommitment=Base64.decode(attr.getNodeValue());
		
		attr=attrs.getNamedItem(webSerialSaltAttr);
		if (attr!=null)
			webSerialSalt=Base64.decode(attr.getNodeValue());
		
		
		
		attr=attrs.getNamedItem(stubSerialAttr);
		if (attr!=null)
			stubSerial=attr.getNodeValue();
		
		attr=attrs.getNamedItem(stubSerialCommitmentAttr);
		if (attr!=null)
			stubSerialCommitment=Base64.decode(attr.getNodeValue());
		
		attr=attrs.getNamedItem(stubSerialSaltAttr);
		if (attr!=null)
			stubSerialSalt=Base64.decode(attr.getNodeValue());
		
		/*
		attr=attrs.getNamedItem(password2Attr);
		if (attr!=null)
			password2=attr.getNodeValue();
		
		attr=attrs.getNamedItem(password2CommitmentAttr);
		if (attr!=null)
			password2Commitment=Base64.decode(attr.getNodeValue());
		
		attr=attrs.getNamedItem(password2SaltAttr);
		if (attr!=null)
			password2Salt=Base64.decode(attr.getNodeValue());
		 */
	}
	
	
	protected void setUp(Attributes attrs) throws Exception {
		for (int i = 0; i < attrs.getLength(); i++) {
            String aName = attrs.getLocalName(i);
            if ("".equals(aName)) aName = attrs.getQName(i);
            
			if (aName.equals(pidAttr))
				pid = Integer.parseInt(attrs.getValue(i));
			else
			if (aName.equals(barcodeSerialAttr))
				barcodeSerial = attrs.getValue(i);
			else
			if (aName.equals(barcodeSerialCommitmentAttr))
				barcodeSerialCommitment = Base64.decode(attrs.getValue(i));
			else
			if (aName.equals(barcodeSerialSaltAttr))
				barcodeSerialSalt = Base64.decode(attrs.getValue(i));
			else
			if (aName.equals(webSerialAttr))
				webSerial=attrs.getValue(i);
			else
			if (aName.equals(webSerialCommitmentAttr))
				webSerialCommitment = Base64.decode(attrs.getValue(i));
			else
			if (aName.equals(webSerialSaltAttr))
				webSerialSalt = Base64.decode(attrs.getValue(i));
			else
			if (aName.equals(stubSerialAttr))
				stubSerial=attrs.getValue(i);
			else
			if (aName.equals(stubSerialCommitmentAttr))
				stubSerialCommitment = Base64.decode(attrs.getValue(i));
			else
			if (aName.equals(stubSerialSaltAttr))
				stubSerialSalt = Base64.decode(attrs.getValue(i));
			/*
			else
			if (aName.equals(password2Attr))
				password2=attrs.getValue(i);
			else
			if (aName.equals(password2CommitmentAttr))
				password2Commitment = Base64.decode(attrs.getValue(i));
			else
			if (aName.equals(password2SaltAttr))
				password2Salt = Base64.decode(attrs.getValue(i));
			*/			
		}		
	}

	public String getBarcodeSerial() {
		return barcodeSerial;
	}

	public void setBarcodeSerial(String barcodeSerial) {
		this.barcodeSerial = barcodeSerial;
	}

	public String getWebSerial() {
		return webSerial;
	}

	public void setWebSerial(String chitSerial) {
		this.webSerial = chitSerial;
	}

	public byte[] getWebSerialCommitment() {
		return webSerialCommitment;
	}

	public void setWebSerialCommitment(byte[] chitSerialCommitment) {
		this.webSerialCommitment = chitSerialCommitment;
	}

	public byte[] getWebSerialSalt() {
		return webSerialSalt;
	}

	public void setWebSerialSalt(byte[] chitSerialSalt) {
		this.webSerialSalt = chitSerialSalt;
	}

	public String getStubSerial() {
		return stubSerial;
	}

	public void setStubSerial(String password1) {
		this.stubSerial = password1;
	}

	public byte[] getStubSerialCommitment() {
		return stubSerialCommitment;
	}

	public void setStubSerialCommitment(byte[] password1Commitment) {
		this.stubSerialCommitment = password1Commitment;
	}

	public byte[] getStubSerialSalt() {
		return stubSerialSalt;
	}

	public void setStubSerialSalt(byte[] password1Salt) {
		this.stubSerialSalt = password1Salt;
	}
/*
	public String getPassword2() {
		return password2;
	}

	public void setPassword2(String password2) {
		this.password2 = password2;
	}

	public byte[] getPassword2Commitment() {
		return password2Commitment;
	}

	public void setPassword2Commitment(byte[] password2Commitment) {
		this.password2Commitment = password2Commitment;
	}

	public byte[] getPassword2Salt() {
		return password2Salt;
	}

	public void setPassword2Salt(byte[] password2Salt) {
		this.password2Salt = password2Salt;
	}
*/	

	public byte[] getBarcodeSerialCommitment() {
		return barcodeSerialCommitment;
	}

	public void setBarcodeSerialCommitment(byte[] barcodeSerialCommitment) {
		this.barcodeSerialCommitment = barcodeSerialCommitment;
	}

	public byte[] getBarcodeSerialSalt() {
		return barcodeSerialSalt;
	}

	public void setBarcodeSerialSalt(byte[] barcodeSerialSalt) {
		this.barcodeSerialSalt = barcodeSerialSalt;
	}

	public int getPid() {
		return pid;
	}

	public void setPid(int pid) {
		this.pid = pid;
	}

	public String toString() {
		StringBuffer ret=new StringBuffer("");

		ret.append("\t\t\t<ballot");
		if (pid!=-1) {
			ret.append(" "+pidAttr+"=\""+pid+"\"");
		}
		if (barcodeSerial!=null) {
			ret.append(" "+barcodeSerialAttr+"=\""+barcodeSerial+"\"");
		}
		if (barcodeSerialCommitment!=null) {
			ret.append(" "+barcodeSerialCommitmentAttr+"=\""+new String(Base64.encode(barcodeSerialCommitment))+"\"");
		}
		if (barcodeSerialSalt!=null) {
			ret.append(" "+barcodeSerialSaltAttr+"=\""+new String(Base64.encode(barcodeSerialSalt))+"\"");
		}
		
		if (webSerial!=null) {
			ret.append(" "+webSerialAttr+"=\""+webSerial+"\"");
		}
		if (webSerialCommitment!=null) {
			ret.append(" "+webSerialCommitmentAttr+"=\""+new String(Base64.encode(webSerialCommitment))+"\"");
		}
		if (webSerialSalt!=null) {
			ret.append(" "+webSerialSaltAttr+"=\""+new String(Base64.encode(webSerialSalt))+"\"");
		}
		
		
		if (stubSerial!=null) {
			ret.append(" "+stubSerialAttr+"=\""+stubSerial+"\"");
		}
		if (stubSerialCommitment!=null) {
			ret.append(" "+stubSerialCommitmentAttr+"=\""+new String(Base64.encode(stubSerialCommitment))+"\"");
		}
		if (stubSerialSalt!=null) {
			ret.append(" "+stubSerialSaltAttr+"=\""+new String(Base64.encode(stubSerialSalt))+"\"");
		}
		/*
		if (password2!=null) {
			ret.append(" "+password2Attr+"=\""+password2+"\"");
		}
		if (password2Commitment!=null) {
			ret.append(" "+password2CommitmentAttr+"=\""+new String(Base64.encode(password2Commitment))+"\"");
		}
		if (password1Salt!=null) {
			ret.append(" "+password2SaltAttr+"=\""+new String(Base64.encode(password2Salt))+"\"");
		}
		*/
		ret.append(">\n");
		return ret.toString();
	}
	
	public static String getEndBallotTag() {
		return "\t\t\t</ballot>\n";
	}
}
