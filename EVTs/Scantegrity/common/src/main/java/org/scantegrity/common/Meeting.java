package org.scantegrity.common;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.math.BigInteger;
import java.security.KeyPair;
import java.security.KeyPairGenerator;
import java.security.MessageDigest;
import java.security.SecureRandom;
import java.security.cert.X509Certificate;
import java.util.Date;
import java.util.Hashtable;
import java.util.TreeMap;
import java.util.Vector;

import javax.crypto.spec.SecretKeySpec;
import javax.security.auth.x500.X500Principal;
import javax.xml.XMLConstants;
import javax.xml.transform.Source;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamSource;
import javax.xml.validation.Schema;
import javax.xml.validation.SchemaFactory;

import org.bouncycastle.asn1.x509.BasicConstraints;
import org.bouncycastle.asn1.x509.GeneralName;
import org.bouncycastle.asn1.x509.GeneralNames;
import org.bouncycastle.asn1.x509.KeyUsage;
import org.bouncycastle.asn1.x509.X509Extensions;
import org.bouncycastle.cms.CMSProcessableFile;
import org.bouncycastle.cms.CMSSignedData;
import org.bouncycastle.cms.CMSSignedDataGenerator;
import org.bouncycastle.cms.CMSSignedGenerator;
import org.bouncycastle.util.encoders.Base64;
import org.bouncycastle.x509.X509V3CertificateGenerator;
import org.scantegrity.common.ballotstandards.Constants;
import org.scantegrity.common.ballotstandards.basic.Answer;
import org.scantegrity.common.ballotstandards.basic.Question;
import org.scantegrity.common.ballotstandards.basic.Section;
import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;
import org.scantegrity.common.ballotstandards.electionSpecification.exceptions.ESException;
import org.scantegrity.common.RowPermutation;

import org.w3c.dom.Document;
import org.xml.sax.SAXException;


/**
 * General framework for all the meetings. Needs m1into read the number of ballots, the
 * number of D tables, the public constant and eventually the partitions. If the partitions are
 * not specified (or specified in a file that cannot be read), by default all the questions are
 * in the same partition.
 * @author stefan
 *
 */
public class Meeting {

	public static boolean CheckagainsSchema=false;
	public static String MeetingOneInSchema="MeetingOneIn.xsd";
	public static SchemaFactory schemaFactory = SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI);
	
	protected SecretKeySpec mk1 = null;
	protected SecretKeySpec mk2 = null;
	protected byte[] c = null;
	protected ElectionSpecification es = null;
	protected int numberOfBallots = 0;
	protected int numberOfDs = 0;	
	
	protected Vector<Vector<Integer>> partitions=null;
	
	protected MarkPermutations markPerm=null;
	
	protected TreeMap<Integer,Drow> drows=null;
	protected TreeMap<Integer,Prow> prows=null;
	protected TreeMap<Integer,Rrow> rrows=null;
	
	protected OutputStream fos=System.out;
	
	protected boolean withSignatures=false;
	
	private String m1inDir=null;
	
	/** 
	 * Initializes the meeting with mk1=mk2=c={0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15},
	 * 100 ballots, 2 D tables
	 * Creates a default Election Specification (4 questions, 1 out of 2, 1 out of 5, 3 out of 6, rank 3 out of 4)
	 */
	public Meeting() {
		byte[] mk1 = {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15};
		byte[] mk2 = {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15};
		byte[] c   = {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15};

		Hashtable<String,Section> sections=new Hashtable<String, Section>();
		//by defauld there is only one section
		Section section=new Section();
		section.setId(0+"");
		section.setPossition(1);
		Hashtable<String, Question> questions = new Hashtable<String, Question>();

		{ //first question - Yes/No
			Question question=new Question();
			question.setId("0");
			question.setPossition(1);
			question.setTypeOfAnswer(Constants.ONE_ANSWER);
			question.setMax(1);
			
			Hashtable<String, Answer> answers=new Hashtable<String, Answer>();
			for (int a=0;a<2;a++) {
				Answer answer=new Answer();
				answer.setId(a+"");
				answer.setPossition(a+1);
				answers.put(answer.getId(), answer);
			}
			question.setAnswers(answers);
			questions.put(question.getId(), question);
		}

		{ //second question - Choose one out of 5
			Question question=new Question();
			question.setId("0");
			question.setPossition(1);
			question.setTypeOfAnswer(Constants.ONE_ANSWER);
			question.setMax(1);
			
			Hashtable<String, Answer> answers=new Hashtable<String, Answer>();
			for (int a=0;a<5;a++) {
				Answer answer=new Answer();
				answer.setId(a+"");
				answer.setPossition(a+1);
				answers.put(answer.getId(), answer);
			}
			question.setAnswers(answers);
			questions.put(question.getId(), question);
		}
		
		{ //thirs question - choose 3 out of 6
			Question question=new Question();
			question.setId("0");
			question.setPossition(1);
			question.setTypeOfAnswer(Constants.MULTIPLE_ANSWERS);
			question.setMax(3);
			
			Hashtable<String, Answer> answers=new Hashtable<String, Answer>();
			for (int a=0;a<3;a++) {
				Answer answer=new Answer();
				answer.setId(a+"");
				answer.setPossition(a+1);
				answers.put(answer.getId(), answer);
			}
			question.setAnswers(answers);
			questions.put(question.getId(), question);
		}
		
		{ //fourth question - rank 3 out of 4
			Question question=new Question();
			question.setId("0");
			question.setPossition(1);
			question.setTypeOfAnswer(Constants.RANK);
			question.setMax(3);
			
			Hashtable<String, Answer> answers=new Hashtable<String, Answer>();
			for (int a=0;a<4;a++) {
				Answer answer=new Answer();
				answer.setId(a+"");
				answer.setPossition(a+1);
				answers.put(answer.getId(), answer);
			}
			question.setAnswers(answers);
			questions.put(question.getId(), question);
		}
		
		section.setQuestions(questions);
		sections.put(section.getId(), section);
		
		es=new ElectionSpecification("PunchScanDemo",sections);

		setUp(c,es,100,2);
		init(mk1,mk2);
	}
	

	/** 
	 * @param confFile - the file containing MetingOneIn.xml
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown 
	 */
	public Meeting(String confFile) throws Exception {
		m1inDir=new File(confFile).getParentFile().getAbsolutePath();
		
		Document doc = Util.DomParse(confFile);
		setUp(doc);
	}

	/** 
	 * @param doc - the xml document containing MeetingOneIn.xml
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown 
	 */
	public Meeting(Document doc) throws Exception{
		setUp(doc);
	}

	/** 
	 * Sets the two master keys from raw material
	 * @param mk1 - master key 1
	 * @param mk2 - master key 2
	 */
	public void init(byte[] mk1,byte[] mk2) {
		this.mk1 = new SecretKeySpec(mk1,"AES");
		this.mk2 = new SecretKeySpec(mk2,"AES");
		init(this.mk1,this.mk2);	
	}

	/**
	 * sets the two master key
	 * @param mk1 - master key 1
	 * @param mk2 - master key 2
	 */
	public void init(SecretKeySpec mk1,SecretKeySpec mk2) {
		this.mk1 = mk1;
		this.mk2 = mk2;
		markPerm = new MarkPermutations(this.mk1,this.mk2,c,es,partitions);		
	}	
	
	private void setUp(byte[] c,ElectionSpecification es, int numberOfBallots, int numberOfDs) {
		this.c = c;
		this.es = es;
		this.numberOfBallots = numberOfBallots;
		this.numberOfDs = numberOfDs;		
	}
	
	private void setUp(Document doc) throws ESException, SAXException, IOException {
		if (Meeting.CheckagainsSchema) {			
		    Source schemaSource = new StreamSource(getClass().getResourceAsStream(Meeting.MeetingOneInSchema));
		    Schema schema = Meeting.schemaFactory.newSchema(schemaSource);
		    schema.newValidator().validate(new DOMSource(doc));
		}
		
		byte[] c = Base64.decode(doc.getElementsByTagName("constant").item(0).getFirstChild().getNodeValue());
		String esSpecPath = doc.getElementsByTagName("electionSpec").item(0).getFirstChild().getNodeValue();
		
		if (! new File(esSpecPath).isAbsolute())
			esSpecPath=m1inDir+"/"+esSpecPath;
		
		ElectionSpecification es = new ElectionSpecification(esSpecPath);
		int numberOfBallots = Integer.parseInt(doc.getElementsByTagName("noBallots").item(0).getFirstChild().getNodeValue());
		int numberOfDs = Integer.parseInt(doc.getElementsByTagName("noDs").item(0).getFirstChild().getNodeValue());
		setUp(c,es,numberOfBallots,numberOfDs);
		String partitionFile=null;
		try {
			partitionFile=doc.getElementsByTagName("partitions").item(0).getFirstChild().getNodeValue();
			
			if (! new File(partitionFile).isAbsolute())
				partitionFile=m1inDir+"/"+partitionFile;

			
		} catch (NullPointerException ex) {
			System.out.println("No partition file found; using a single partition");
		}
		partitions=Util.setPartitions(es,partitionFile);		
	}

	protected void computeP() throws Exception {
		//go through the prows in order
		fos.write("\t\t<print>\n".getBytes());				
		for (int i:prows.keySet()) {
			Prow prow=prows.get(i);
			computeP(prow);
			
			//write prow to disk
			fos.write(prow.toString().getBytes());
			
			//free some memory
			prow.setC1(null);
			prow.setC2(null);
			prow.setS1(null);
			prow.setS2(null);
		}
		fos.write("\t\t</print>\n".getBytes());
	}
	
	/**
	 * 
	 * @param prow
	 * @return
	 * @throws Exception
	 */
	protected void computeP(Prow prow) throws Exception {
		byte[] serial = (prow.getId()+"").getBytes();
		
		if (prow.getChosenPage().equals(Prow.ChosenPage.TOP)
				|| prow.getChosenPage().equals(Prow.ChosenPage.BOTH)
			) {
			prow.setPage1(markPerm.getP1(serial));
			if (Prow.getOperation().equals(Prow.Operation.OPEN_COMMITMENTS)
					|| Prow.getOperation().equals(Prow.Operation.PUBLISH_COMMITMENTS)
					) {
				prow.setS1(Commitments.saltP1(mk1,mk2,c,serial).getEncoded());
				if (Prow.getOperation().equals(Prow.Operation.PUBLISH_COMMITMENTS)) {
					prow.setC1(Commitments.commitP(prow.getS1(),c,serial,prow.getPage1()));
				}
			}
		}

		if (prow.getChosenPage().equals(Prow.ChosenPage.BOTTOM)
				|| prow.getChosenPage().equals(Prow.ChosenPage.BOTH)
			) {				
			prow.setPage2(markPerm.getP2(serial));
			if (Prow.getOperation().equals(Prow.Operation.OPEN_COMMITMENTS)
					|| Prow.getOperation().equals(Prow.Operation.PUBLISH_COMMITMENTS)
					) {
				prow.setS2(Commitments.saltP2(mk1,mk2,c,serial).getEncoded());
				if (Prow.getOperation().equals(Prow.Operation.PUBLISH_COMMITMENTS)) {
					prow.setC2(Commitments.commitP(prow.getS2(),c,serial,prow.getPage2()));
				}
			}
		}
	}

	
	
	//compute D for all partitions, eventually put them into separate files ?	
	protected void computeD() throws Exception { 
		int[] masterPerm;		
		for (byte partitionId=0;partitionId<partitions.size();partitionId++) {
			fos.write(("\t\t<partition id=\""+partitionId+"\">\n").getBytes());	
			fos.write("\t\t\t<decrypt>\n".getBytes());
			//compute the D1 permutation
			//this is the permutation that maps D1 to D5
			masterPerm = RowPermutation.permuteD1D5(mk1,mk2,c,0,numberOfBallots-1,partitionId);
//Util.print(mk1.getEncoded());			
//Util.print(mk2.getEncoded());
//System.out.println(new String(c));
//Util.print(masterPerm);
			for (byte dNo=0;dNo<numberOfDs;dNo++) {
				//for one instance of the D table, compute the flips and the commitments.
				fos.write(("\t\t\t\t<instance id=\""+dNo+"\">\n").getBytes());
				drows=new TreeMap<Integer, Drow>();
				
				int[] d1Perm = RowPermutation.permuteD1(mk1,mk2,c,dNo,0,numberOfBallots-1,partitionId);
				int[] d1PermInv = Util.getInverse(d1Perm);
				for (int pid:prows.keySet()) {
					Drow drow=new Drow();
					drow.setId(d1PermInv[pid]);
					drow.setChosenSide(Drow.ChosenSide.BOTH);
					
					drows.put(drow.getId(), drow);
				}
				computeD(masterPerm,dNo,partitionId);
				fos.write("\t\t\t\t</instance>\n".getBytes());			
			}
			fos.write("\t\t\t</decrypt>\n".getBytes());
			
			if (Drow.getOperation().equals(Drow.Operation.PUBLISH_RESULTS)) {
				fos.write("\t\t\t<results>\n".getBytes());
				computeR(masterPerm,partitionId);
				//computeR();
				fos.write("\t\t\t</results>\n".getBytes());				
			}
			fos.write(("\t\t</partition>\n").getBytes());
		}
	}
	
	protected void computeD(int[] masterPerm,byte dNo,byte partitionId) throws Exception {
		int[] d1Perm = RowPermutation.permuteD1(mk1,mk2,c,dNo,0,numberOfBallots-1,partitionId);	

		for (int did:drows.keySet()) {			
			Drow drow=drows.get(did);
			drow.setPid(d1Perm[did]);
			drow.setRid(masterPerm[d1Perm[did]]);
			
			computeD(drow, prows!=null?prows.get(drow.getPid()):null, dNo, partitionId);
			
			fos.write(drow.toString().getBytes());
			
			//free some memory by removing the drow from the drows
			drows.put(drow.getId(), null);
			drow=null;
		}
	}

	protected void computeD(Drow drow, Prow prow, byte dInstance,byte partitionId) throws Exception {
		byte[] serial = Integer.toString(drow.getId()).getBytes();
		
		if (drow.getChosenSide().equals(Drow.ChosenSide.LEFT)
				|| drow.getChosenSide().equals(Drow.ChosenSide.BOTH)
			) {
			drow.setPage1(markPerm.getD2(serial, dInstance, partitionId));
			if (Drow.getOperation().equals(Drow.Operation.OPEN_COMMITMENTS)
					|| Drow.getOperation().equals(Drow.Operation.PUBLISH_COMMITMENTS)
					) {
				drow.setS1(Commitments.saltDRowLeft(mk1,mk2,c,partitionId,dInstance,serial).getEncoded());
				if (Drow.getOperation().equals(Drow.Operation.PUBLISH_COMMITMENTS)) {
					drow.setC1(Commitments.commitD(drow.getS1(), c, partitionId, dInstance, serial, drow.getPid(), drow.getPage1()));
				}
			}
		}

		if (drow.getChosenSide().equals(Drow.ChosenSide.RIGHT)
				|| drow.getChosenSide().equals(Drow.ChosenSide.BOTH)
			) {
			if (prow==null) {
				prow=new Prow();
				prow.setId(drow.getPid());
			}
			
			if (prow.getPage1()==null) {
				prow.setChosenPage(Prow.ChosenPage.TOP);
				computeP(prow);
			}
			if (prow.getPage2()==null) {
				prow.setChosenPage(Prow.ChosenPage.BOTTOM);
				computeP(prow);
			}
			if (drow.getPage1()==null) {
				drow.setPage1(markPerm.getD2(serial, dInstance, partitionId));
			}
			drow.setPage2(markPerm.getD4(prow.getPage1(), prow.getPage2(), drow.getPage1(), partitionId));
			if (Drow.getOperation().equals(Drow.Operation.OPEN_COMMITMENTS)
					|| Drow.getOperation().equals(Drow.Operation.PUBLISH_COMMITMENTS)
					) {
				drow.setS2(Commitments.saltDRowRight(mk1,mk2,c,partitionId,dInstance,serial).getEncoded());
				if (Drow.getOperation().equals(Drow.Operation.PUBLISH_COMMITMENTS)) {
					drow.setC2(Commitments.commitD(drow.getS2(), c, partitionId, dInstance, serial, drow.getRid(), drow.getPage2()));
				}
			}
		}
		
		if (Drow.getOperation().equals(Drow.Operation.PUBLISH_RESULTS)) {
			drow.setVote(markPerm.computeD3(prow.getVote(),drow.getPage1(),partitionId));
		}
	}
/*
	void computeR(int[] masterPerm,byte partitionId) throws Exception {
		for (int pid:prows.keySet()) {
			rrows.put(masterPerm[pid], new Rrow());
		}
		computeR(masterPerm,partitionId);
	}	
*/

	protected void computeR() throws Exception { 
		int[] masterPerm;
		for (byte partitionId=0;partitionId<partitions.size();partitionId++) {
			masterPerm = RowPermutation.permuteD1D5(mk1,mk2,c,0,numberOfBallots-1,partitionId);
			rrows=new TreeMap<Integer, Rrow>();
			for (int pid:prows.keySet()) {
				Rrow rrow=new Rrow();
				rrow.setId(masterPerm[pid]);
				rrows.put(rrow.getId(), rrow);
			}
			computeR(masterPerm,partitionId);			
		}
	}
	
	
	protected void computeR(int[] masterPerm,byte partitionId) throws Exception {
		rrows=new TreeMap<Integer, Rrow>();
		for (int pid:prows.keySet()) {
			Rrow rrow=new Rrow();
			rrow.setId(masterPerm[pid]);
			rrows.put(rrow.getId(), rrow);
		}			
		
		int[] masterPermInv=Util.getInverse(masterPerm);
		for (int rid:rrows.keySet()) {
			Rrow rrow=rrows.get(rid);
			
			computeR(prows.get(masterPermInv[rid]),rrow,partitionId);
			
			fos.write(rrow.toString().getBytes());
		}
	}
	
	protected void computeR(Prow prow,Rrow rrow,byte partitionId) throws Exception {	
		byte[] p1Inverse=markPerm.getInversePartition(markPerm.project(prow.getPage1(), partitionId), partitionId);
		byte[] p2ComposedWithP1Inverse=markPerm.compose(markPerm.project(prow.getPage2(),partitionId),p1Inverse, partitionId);
		
		byte[] clearTextVote=markPerm.computeD3(prow.getVote(),p2ComposedWithP1Inverse,partitionId);
		
		rrow.setVote(clearTextVote);

	}

	public int getNumberOfBallots() {
		return numberOfBallots;
	}


	public void setNumberOfBallots(int numberOfBallots) {
		this.numberOfBallots = numberOfBallots;
	}


	public int getNumberOfDs() {
		return numberOfDs;
	}


	public void setNumberOfDs(int numberOfDs) {
		this.numberOfDs = numberOfDs;
	}


	public ElectionSpecification getEs() {
		return es;
	}


	public void setEs(ElectionSpecification es) {
		this.es = es;
	}

	public Vector<Vector<Integer>> getPartitions() {
		return partitions;
	}

	public void setPartitions(Vector<Vector<Integer>> partitions) {
		this.partitions = partitions;
	}

	public byte[] getC() {
		return c;
	}
	
	/**
	 * Signes a file with the key derived from the masterkeys. 
	 * Produces a new file, with the same same, but with the .sig extenssion
	 * @param inFile
	 * @throws Exception
	 */
	protected void sign(String inFile) throws Exception {
		//hash mk1,mk2,c
		MessageDigest sha = MessageDigest.getInstance("SHA256","BC");
		sha.update(mk1.getEncoded(),0,mk1.getEncoded().length);
		sha.update(mk2.getEncoded(),0,mk2.getEncoded().length);
		sha.update(c,0,c.length);
		byte[] salt = sha.digest();
		
		KeyPairGenerator  kpGen = KeyPairGenerator.getInstance("RSA", "BC");
	    
        kpGen.initialize(2048, new SecureRandom(salt));
    
        KeyPair pair = kpGen.generateKeyPair();
        
        X509Certificate cert=getCert(pair);
        OutputStream out=new BufferedOutputStream(new FileOutputStream("cert.cer"));        
        out.write(SecurityUtil.toPEM(cert).getBytes());
        out.close();
        
        CMSProcessableFile cmsFile=new CMSProcessableFile(new File(inFile));
        CMSSignedDataGenerator gen=new CMSSignedDataGenerator();
        gen.addSigner(pair.getPrivate(), cert, CMSSignedGenerator.DIGEST_SHA256);
        CMSSignedData signed = gen.generate(cmsFile, "BC");
        
        String outFile = inFile.substring(0,inFile.lastIndexOf("."))+".sig";
        out=new BufferedOutputStream(new FileOutputStream(outFile));
        out.write(signed.getEncoded());
        out.close();
	}	
	
	/**
	 * generates a certificate based on the two master keys
	 * @return
	 * @throws Exception
	 */
	protected X509Certificate getCert(KeyPair pair) throws Exception {
        X509V3CertificateGenerator  certGen = new X509V3CertificateGenerator();

        X500Principal cn=new X500Principal("CN=PunchScan Student Voting Authority");
        certGen.setSerialNumber(BigInteger.valueOf(System.currentTimeMillis()));
        certGen.setIssuerDN(cn);
        certGen.setNotBefore(new Date(System.currentTimeMillis() - 50000));
        long validity=60*60*24*30;//30 days
        certGen.setNotAfter(new Date(System.currentTimeMillis() + validity*1000));
        certGen.setSubjectDN(cn);
        certGen.setPublicKey(pair.getPublic());
        certGen.setSignatureAlgorithm("SHA256WithRSAEncryption");
        
        certGen.addExtension(X509Extensions.BasicConstraints, true, new BasicConstraints(false));
        
        certGen.addExtension(X509Extensions.KeyUsage, true, new KeyUsage(KeyUsage.digitalSignature));
        
        certGen.addExtension(X509Extensions.SubjectAlternativeName, false, new GeneralNames(new GeneralName(GeneralName.rfc822Name, "punchscan@lists.umbc.edu")));

        X509Certificate cert = certGen.generate(pair.getPrivate(), "BC");
        
        return cert;        
	}

	public TreeMap<Integer, Prow> getProws() {
		return prows;
	}


	public void setProws(TreeMap<Integer, Prow> prows) {
		this.prows = prows;
	}
}
