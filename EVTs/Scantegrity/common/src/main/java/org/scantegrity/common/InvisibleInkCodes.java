package org.scantegrity.common;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.security.InvalidKeyException;
import java.util.TreeMap;
import java.util.TreeSet;

import javax.crypto.BadPaddingException;
import javax.crypto.Cipher;
import javax.crypto.IllegalBlockSizeException;
import javax.crypto.spec.SecretKeySpec;
import javax.xml.parsers.SAXParser;

import org.scantegrity.common.ballotstandards.Constants;
import org.scantegrity.common.ballotstandards.basic.Question;
import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;
import org.w3c.dom.Document;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

public class InvisibleInkCodes {

	int noCodesPerBallot=0;
		
	protected TreeMap<Integer,Prow> prows=null;
	protected Question[] qs=null;
	
	public static int NumberOfCharectersInACode=3;
	/*
	public static String[] CodesAlphabet={
		"1","2","3","4",
		"5","7","8","9",
		"A","B","C","E",
		"F","G","J",
		"K","L","N","O",
		"P","S","T","U","X",
		"Y"
	};
	 */
	//List of Codes Ron suggested
	public static String[] CodesAlphabet={
		"0","1","2",
		"3","4","5","6","7",
		"8","9"
	};
	
	public static int NumberOfPossibleCodes=(int)Math.pow(CodesAlphabet.length,NumberOfCharectersInACode);
	public static int noBits=(int)Math.round((Math.log(NumberOfPossibleCodes)/Math.log(2)));
	
	//TODO list invalid conbinations in a file
	public static String[] forbidenCodes= {
		"FUCK","SH1T","-REP","-DEM"};
	
	int[] noCodesBeforeQuestion=null;

	protected SecretKeySpec mk1 = null;
	protected SecretKeySpec mk2 = null;
	protected byte[] c = null;
	
	public void init(SecretKeySpec mk1,SecretKeySpec mk2,byte[] c) {
		this.mk1 = mk1;//new SecretKeySpec(mk1,"AES");
		this.mk2 = mk2;//new SecretKeySpec(mk2,"AES");
		this.c=c;
	}
	
	public static void WriteCodes(String outputFile) throws IOException {
		OutputStream pos = new BufferedOutputStream(new FileOutputStream(outputFile));
		pos.write("<xml>\n".getBytes());
		pos.write(("\t<codes numberOfLettersPerCode=\""+InvisibleInkCodes.NumberOfCharectersInACode+"\">\n").getBytes());
		
		for (int i=0;i<InvisibleInkCodes.CodesAlphabet.length;i++) {
			pos.write(("\t\t<code id=\""+i+"\" value=\"").getBytes());
			pos.write(InvisibleInkCodes.CodesAlphabet[i].getBytes());
			pos.write("\"/>\n".getBytes());
		}
		
		pos.write("\t</codes>\n".getBytes());			
		pos.write("</xml>".getBytes());
		pos.close();		
	}

	public static void ReadCodes(String inFile) throws IOException, SAXException {
		Document doc = Util.DomParse(inFile);
		Node codesNode=doc.getElementsByTagName("codes").item(0);
		InvisibleInkCodes.NumberOfCharectersInACode=Integer.parseInt(codesNode.getAttributes().getNamedItem("numberOfLettersPerCode").getNodeValue());
		
		TreeMap<Integer, String> codes=new TreeMap<Integer, String>();
		NodeList codeNodeList=doc.getElementsByTagName("code");
		for (int i=0;i<codeNodeList.getLength();i++) {
			NamedNodeMap codeNode=codeNodeList.item(i).getAttributes();
			codes.put(Integer.parseInt(codeNode.getNamedItem("id").getNodeValue()), new String(codeNode.getNamedItem("value").getNodeValue()));
		}
		
		InvisibleInkCodes.CodesAlphabet=new String[codes.size()];
		int index=0;
		for (int key:codes.keySet()) {
			InvisibleInkCodes.CodesAlphabet[index++]=codes.get(key);
		}
	}

	public InvisibleInkCodes(ElectionSpecification es) {
		qs=es.getOrderedQuestions();
		noCodesPerBallot=0;
		noCodesBeforeQuestion=new int[qs.length+1];
		for (int q=0;q<qs.length;q++) {
				noCodesBeforeQuestion[q]=noCodesPerBallot;
				noCodesPerBallot+=getNoCodesPerQuestion(qs[q]);
		}
		noCodesBeforeQuestion[qs.length]=noCodesPerBallot;
	}
	
	public int getNoCodesBeforeQuestion(int q) {
		return noCodesBeforeQuestion[q];
	}
	
	public int getNoCodesPerQuestion(Question q) {
		if (q.getTypeOfAnswer().compareTo(Constants.RANK)==0) {
			return q.getAnswers().size()*q.getMax();
		}
		return 	q.getAnswers().size();
	}
	
	public InvisibleInkCodes(String pathToPrintsFile, ElectionSpecification es) throws Exception {
		this(es);
		
		if (pathToPrintsFile!=null) {
			MeetingReaderSax mr = new MeetingReaderSax();
	        try {
	            SAXParser saxParser = Util.newSAXParser();
	            saxParser.parse( new File(pathToPrintsFile), mr);
	        } catch (Throwable t) {
	            t.printStackTrace();
	        }        
	        while (!mr.isDoneParsing()) {
	        	Thread.sleep(100);
	        }        
			prows=mr.getProws();
		}
	}
	
	/**
	 * getCode returns one confirmation code that is to be printed on a Ballot.
	 * It creates a PRNG from the serial, question number, rank, and answer
	 * number encrypted with a key generated from entropy provided by election
	 * trustees. The 128 Ciphertext bytes are then reduce into noBits bits to 
	 * produce a confirmation number whose maximum value is less that the max 
	 * number of possible codes.  
	 * 
	 * Because there are 128 bits, we take advantage of that fact, assuming
	 * the RNG is not entirely uniformly distributed, by xor'ing all the 
	 * noBits-sized chunks with each other to mitigate this problem.
	 * 
	 * For many reasons, this code is not a great way to generate confirmation
	 * codes, but we wanted to make minimal changes from the 2009 codebase. It
	 * should provide slightly less than noBits of entropy instead of the 8.5
	 * bits of entropy from the 2009 election. 
	 * 
	 * @param printedSerial
	 * @param qno - question number
	 * @param rank - the rank (column) from IRV, usually 0
	 * @param ano - the answer number (candidate choice)
	 * @param key - the key generated from trustee entropy
	 * @param noBits - number of bits
	 * @param codesAlreadyGenerated - list of codes we can't use.
	 * @return
	 * @throws InvalidKeyException
	 * @throws IllegalBlockSizeException
	 * @throws BadPaddingException
	 */
	public static int getCode(int printedSerial, int qno,int rank, int ano,
								SecretKeySpec key,int noBits, 
								TreeSet<Integer> codesAlreadyGenerated) 
	throws InvalidKeyException, IllegalBlockSizeException, BadPaddingException {
		String m=printedSerial+" "+qno+" "+rank+" "+ano;
		if (m.getBytes().length > 15) System.err.print("M greater than 16!!!");
		SecurityUtil.cipherPkcs5Padding.init(Cipher.ENCRYPT_MODE, key);
		byte[] enc=m.getBytes();
		int ret=0;
		do {
			enc=SecurityUtil.cipherPkcs5Padding.doFinal(enc);
			// All 8 bits from byte 1 shifted left by 2.
			int l_b = (((int)enc[0]) << (24)) >>> (24);
			ret = (l_b << 2);
			
			// Top 2 bits from byte 2, shifted right by 6.
			l_b = (((int)enc[1]) << (24)) >>> (24);
			ret ^= (l_b >>> 6);
			
			/*
			int l_d = Math.max(0, noBits-8);
			int l_pz = l_d;
			for (int i = 0; i < enc.length; i++)
			{
				int l_b = (((int)enc[i]) << (24)) >>> (24);
				//System.out.format("%s\n", Integer.toBinaryString(l_b));
				ret ^= l_b << l_pz;
				// Uncomment next line to stop loop at noBits.
				//if (l_pz >= (noBits-8)) break; 
				if (l_pz > (noBits-8))
				{
					ret ^= l_b >>> (noBits-l_pz);
				}
				l_pz = (l_pz+l_d) % noBits; 
			}
			*/
			
			//Remove the bits we don't need.
			ret <<= (32-noBits);
			ret >>>= (32-noBits);
			//System.out.println("----");
			//System.out.format("%s\n", Integer.toBinaryString(ret));
			//System.out.println("----");
		}
		while (ret>=NumberOfPossibleCodes 
				|| codesAlreadyGenerated.contains(ret));
		
		return ret;
	}
	
	public String[] getNonPermutedSymbols(int printedSerial) throws Exception {
		String[] nonPermutedCodes=new String[noCodesPerBallot];
		int nonPermutedCodesPos=0;
		TreeSet<Integer> codesAlreadyGenerated=new TreeSet<Integer>();
		
		int noRanks=0;
		int codeInt=0;
        for (int qno=0;qno<qs.length;qno++) { 
        	
        	//generate the key for this question;
        	SecretKeySpec key=Commitments.KeyForCodeGeneration(mk1, mk2, c, (printedSerial+"").getBytes(), (qno+"").getBytes(), Commitments.KEY_CONSTANT);
        	
        	codesAlreadyGenerated.clear();
            noRanks=1;
            if (qs[qno].getTypeOfAnswer().compareTo(Constants.RANK)==0)
            	noRanks=qs[qno].getMax();
            for (int rank=0;rank<noRanks;rank++) {                	            		        	
	        	for (int ano=0;ano<qs[qno].getAnswers().size();ano++) {
	        		codeInt=getCode(printedSerial, qno, rank, ano, key, noBits,codesAlreadyGenerated);
	        		codesAlreadyGenerated.add(codeInt);
	        		nonPermutedCodes[nonPermutedCodesPos++]=
	        			intToString(codeInt,CodesAlphabet);
	        	}
            }
        }
				
		return nonPermutedCodes;
	}
		
	public static String intToString(int x,String[] radixChars) {
		int radix=radixChars.length;
		StringBuffer ret=new StringBuffer("");
		while (x>0) {
			ret.append(radixChars[x%radix]);
			x=x/radix;
		}
		while (ret.length()<NumberOfCharectersInACode) {
			ret.append(radixChars[0]);
		}
		return ret.reverse().toString();
	}
	
	public int getNoCodesPerBallot() {
		return noCodesPerBallot;
	}
}