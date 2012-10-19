package org.scantegrity.engine;


import java.io.BufferedOutputStream;
import java.io.FileOutputStream;
import java.util.TreeMap;

import javax.xml.transform.Source;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamSource;
import javax.xml.validation.Schema;

import org.w3c.dom.Document;

import org.scantegrity.common.Drow;
import org.scantegrity.common.InputConstants;
import org.scantegrity.common.Meeting;
import org.scantegrity.common.Prow;
import org.scantegrity.common.Util;

/**
 * Published the commitmentd to the tables on the PunchBoard 
 * @author stefan
 *
 */
public class MeetingOne extends Meeting {	 
	
	public static String MeetingOneOutSchema="MeetingOneOut.xsd";
	
	public MeetingOne() throws Exception {
		super();
	}
	
	public MeetingOne(String confFile) throws Exception {
		super(confFile);
	}

	public MeetingOne(Document doc) throws Exception {
		super(doc);
	}
	
	/** 
	 * For all the D tables, publishes commitments
	 * 
	 * @param outputFile the xml file to be written
	 * @throws Exception if the meeting wasn't initialized with the two master keys
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
		Prow.setOperation(Prow.Operation.PUBLISH_COMMITMENTS);
		computeP();

		Drow.setOperation(Drow.Operation.PUBLISH_COMMITMENTS);
		computeD();

//closing the file with the output			
fos.write("\t</database>\n".getBytes());
fos.write("</xml>".getBytes());
fos.close();

		if (Meeting.CheckagainsSchema) {
			Document doc = Util.DomParse(outputFile);			
		    Source schemaSource = new StreamSource(getClass().getResourceAsStream(MeetingOne.MeetingOneOutSchema));
		    Schema schema = Meeting.schemaFactory.newSchema(schemaSource);
		    schema.newValidator().validate(new DOMSource(doc));         						
		}
		
		if (withSignatures)
			sign(outputFile);
	}
		
	
	protected void computeP() throws Exception {
		prows=new TreeMap<Integer, Prow>();
		for (int i=0;i<numberOfBallots;i++) {
			Prow prow=new Prow();
			prow.setId(i);
			prow.setChosenPage(Prow.ChosenPage.BOTH);
			prows.put(i, prow);
		}
		super.computeP();
	}
	
	/**
	 * debig method
	 * @param args
	 * @throws Exception
	 */
	public static void main(String[] args) throws Exception {
		if (args.length < 1) {
			System.out.println("MeetingOne MeetingOneIn.xml");
			return;
		}
		MeetingOne m1 = new MeetingOne(args[0]);
		m1.init(InputConstants.MK1,InputConstants.MK2);
		m1.go(args[1]);
	}
}
