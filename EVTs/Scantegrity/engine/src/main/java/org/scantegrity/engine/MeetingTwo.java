package org.scantegrity.engine;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.OutputStream;
import java.util.Set;

import javax.xml.parsers.SAXParser;
import javax.xml.transform.Source;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamSource;
import javax.xml.validation.Schema;

import org.w3c.dom.Document;

import org.scantegrity.common.Drow;
import org.scantegrity.common.InputConstants;
import org.scantegrity.common.Meeting;
import org.scantegrity.common.MeetingReaderSax;
import org.scantegrity.common.Prow;
import org.scantegrity.common.Util;

/**
 * Given a set of ballots in the P table, it opens all the commitments related to them
 * (in the P table and in all the D tables)
 * @author stefan
 *
 */
public class MeetingTwo extends Meeting {	 
	
	public static String MeetingTwoInSchema="MeetingTwoIn.xsd";
	public static String MeetingTwoOutSchema="MeetingTwoOut.xsd";
	public static String MeetingTwoPrintsSchema="MeetingTwoPrints.xsd";
	public static String SerialMapSchema="SerialMap.xsd";
	
	public MeetingTwo() throws Exception {
		super();
	}
	
	public MeetingTwo(String confFile) throws Exception {
		super(confFile);
	}

	public MeetingTwo(Document doc) throws Exception {
		super(doc);
	}
	
	/**
	 * reads in memory all the ballots that should be opened and calls go(outFile)
	 * @param inFilePath
	 * @param outFile
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown
	 */
	public void go(String inFilePath,String outFile) throws Exception {
		if (Meeting.CheckagainsSchema) {
			Document doc = Util.DomParse(inFilePath);			
		    Source schemaSource = new StreamSource(getClass().getResourceAsStream(MeetingTwo.MeetingTwoInSchema));
		    Schema schema = Meeting.schemaFactory.newSchema(schemaSource);
		    schema.newValidator().validate(new DOMSource(doc));         						
		}
		
			
		
		MeetingReaderSax mr = new MeetingReaderSax();
        //try {
            SAXParser saxParser = Util.newSAXParser();
            saxParser.parse( new File(inFilePath), mr);
        //} catch (Throwable t) {
//            t.printStackTrace();
//        }
        
        while (!mr.isDoneParsing()) {
        	Thread.sleep(100);
        }        
		prows = mr.getProws();
		
		go(outFile);
	}	

	/**
	 * Precondition: it must have in memory the set of P rows to be opened 
	 * @param outputFile - where the xml file with the opened commitment is written
	 * @throws Exception itthe meeting wasn't initialized with the two master keys
	 */
	public void go(String outputFile) throws Exception {
		if (mk1==null || mk2==null)
			throw new Exception("Meeting was not initialized with master keys.");
				
//This is where the output of Meeting one will be written
fos = new BufferedOutputStream(new FileOutputStream(outputFile));
fos.write("<xml>\n".getBytes());
fos.write("\t<database>\n".getBytes());		
		
		/*
		 * The order of the operations should be
		 *  - Compute the P table (P1,P2 and the commitments)
		 *  - compute the permutations of D
		 *  - for each D instance
		 *  	- compute the rows in D in sequence (on INDEX, not serial) and commit to each row
		 *  	- compute the commitments to each column
		 */
		
		//compute the flips in the P table and the commitments to the flips
		//p[BallotId][top]
		
		Prow.setOperation(Prow.Operation.OPEN_COMMITMENTS);
		super.computeP();
		
		Drow.setOperation(Drow.Operation.OPEN_COMMITMENTS);
		super.computeD();
		
//closing the file with the output			
fos.write("\t</database>\n".getBytes());
fos.write("</xml>".getBytes());
fos.close();

		if (Meeting.CheckagainsSchema) {
			Document doc = Util.DomParse(outputFile);			
		    Source schemaSource = new StreamSource(getClass().getResourceAsStream(MeetingTwo.MeetingTwoOutSchema));
		    Schema schema = Meeting.schemaFactory.newSchema(schemaSource);
		    schema.newValidator().validate(new DOMSource(doc));         						
		}

		if (withSignatures)
			sign(outputFile);
	}
		

	/**
	 * Takes all the ballots that have not been opened and publishes them in
	 * clear text in a file that is going to be used for producing (printing)
	 * ballots. It remaps tehm to have continous numbers, starting from 0.
	 *
	 * This method must be explictly called when running meeting two.
	 *  
	 * @param printOutputFile
	 * @param mapOutputFile
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown
	 */
	public void makePrints(String printOutputFile,String mapOutputFile) throws Exception {
		//eliminate the spoiled ballots
		Set<Integer> challenges=prows.keySet();
		int[] prints=new int[numberOfBallots-challenges.size()];
		int printsPos=0;
		for (int i=0;i<numberOfBallots;i++) {
			if (!challenges.contains(i))
				prints[printsPos++]=i;
		}

OutputStream pos = new BufferedOutputStream(new FileOutputStream(printOutputFile));
pos.write("<xml>\n".getBytes());
pos.write("\t<print>\n".getBytes());

OutputStream mos = new BufferedOutputStream(new FileOutputStream(mapOutputFile));
mos.write("<xml>\n".getBytes());
mos.write("\t<print>\n".getBytes());

		for (int i=0;i<prints.length;i++) {
			byte[] serial = Integer.toString(prints[i]).getBytes();
			
			byte[] p1 = markPerm.getP1(serial);
			byte[] p2 = markPerm.getP2(serial);

pos.write(("\t\t<row id=\""+i+"\" p1=\"").getBytes());
Util.write(p1,pos);
pos.write("\" p2=\"".getBytes());
Util.write(p2,pos);
pos.write(("\"/>\n").getBytes());

mos.write(("\t\t<row id=\""+prints[i]+"\" serial=\""+i+"\"/>\n").getBytes());
		}
pos.write("\t</print>\n".getBytes());			
pos.write("</xml>".getBytes());
pos.close();

mos.write("\t</print>\n".getBytes());			
mos.write("</xml>".getBytes());
mos.close();


		if (Meeting.CheckagainsSchema) {
			Document doc = Util.DomParse(printOutputFile);			
		    Source schemaSource = new StreamSource(getClass().getResourceAsStream(MeetingTwo.MeetingTwoPrintsSchema));
		    Schema schema = Meeting.schemaFactory.newSchema(schemaSource);
		    schema.newValidator().validate(new DOMSource(doc));         						
		    
		    doc = Util.DomParse(mapOutputFile);			
		    schemaSource = new StreamSource(getClass().getResourceAsStream(MeetingTwo.SerialMapSchema));
		    schema = Meeting.schemaFactory.newSchema(schemaSource);
		    schema.newValidator().validate(new DOMSource(doc));
		}

		if (withSignatures) {
			sign(printOutputFile);
			sign(mapOutputFile);
		}
	}
	
	
	/**
	 * debug method
	 * @param args
	 * @throws Exception
	 */
	public static void main(String[] args) throws Exception {
		if (args.length < 2) {
			System.out.println("MeetingOne MeetingOneIn.xml MeetingTwoIn.xml");
			return;
		}
		MeetingTwo m2 = new MeetingTwo(args[0]);
		m2.init(InputConstants.MK1,InputConstants.MK2);		
		m2.go(args[1],args[2]);
		m2.makePrints(args[3],args[4]);
	}
}
