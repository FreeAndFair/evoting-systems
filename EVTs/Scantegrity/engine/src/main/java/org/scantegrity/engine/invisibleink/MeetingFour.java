package org.scantegrity.engine.invisibleink;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Hashtable;
import java.util.TreeMap;

import org.w3c.dom.Document;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;


import org.scantegrity.common.BallotRow;
import org.scantegrity.common.InputConstants;
import org.scantegrity.common.InvisibleInkCodes;
import org.scantegrity.common.Prow;
import org.scantegrity.common.RowPermutation;
import org.scantegrity.common.Util;

public class MeetingFour extends org.scantegrity.engine.MeetingFour {

	String printAuditCodes=InputConstants.PrintAuditCodes;
	String alphabet=InputConstants.Codes;
	String meetingOneIn=InputConstants.MeetingOneIn;
	
	InvisibleInkCodes invisibleInkCodes=null; 
	
	public MeetingFour() throws Exception {
		super();
	}
	
	public MeetingFour(String confFile) throws Exception {
		super(confFile);
		this.meetingOneIn=confFile;
	}

	public MeetingFour(Document doc) throws Exception {
		super(doc);
	}

	protected void revealPrintedCodesForUnvoted(TreeMap<Integer, Prow> prows) {
		//reveal all the codes, including the chit serial numbers, passwords and confirmation codes
		MeetingThree m3=null;
		try {
			m3 = new MeetingThree(meetingOneIn);
		} catch (Exception e) {
			e.printStackTrace();
		}
		m3.setProws(this.getProws());
		m3.init(mk1, mk2);
		
		try {
			m3.revealAllSymbolsOnSpoiledBallots(prows, alphabet, printAuditCodes);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
/*	
	public void webSerialOrBarcodeSerialToPid(String inFile, String outFile) throws Exception {
		Document doc=Util.DomParse(inFile);
		
		String serialPrefix="";
		
		//generate the barcodes
		String[] barCodeSerials=RowPermutation.generateBarcodeSerialNumbers(mk1, mk2, c, serialPrefix, 100000, 999999, numberOfBallots);

		//generate the chit numbers
		String[] webSerials=RowPermutation.generateWebSerials(mk1, mk2, c, serialPrefix, 100000, 999999, numberOfBallots);

		Hashtable<String, Integer> webSerialToPid=new Hashtable<String, Integer>();
		Hashtable<String, Integer> barCodeSerialToPid=new Hashtable<String, Integer>();

		for (int i=0;i<webSerials.length;i++) {
			String webSerial=webSerials[i];
			webSerialToPid.put(webSerial, i);
		}

		for (int i=0;i<barCodeSerials.length;i++) {
			String barCode=barCodeSerials[i];
			barCodeSerialToPid.put(barCode, i);
		}
		
		BufferedOutputStream bos=new BufferedOutputStream(new FileOutputStream(outFile));
		bos.write("<xml>".getBytes());
		bos.write("\t<database>".getBytes());
		bos.write("\t\t<print>".getBytes());

		
		NodeList rowNodes=doc.getElementsByTagName("row");
		for (int i=0;i<rowNodes.getLength();i++) {
			BallotRow row=new BallotRow(rowNodes.item(i));
			
			if (row.getBarcodeSerial()==null && row.getWebSerial()==null) {
				throw new Exception("row "+row.toString()+" does not have a webSerial or a barCodeSerial");
			}
			
			int pid=-1;
			if (row.getBarcodeSerial()!=null) {
				pid=barCodeSerialToPid.get(row.getBarcodeSerial());
			}
			
			if (row.getWebSerial()!=null) {
				if (pid!=-1 && webSerialToPid.get(row.getWebSerial())!=pid) {
					throw new Exception("for row "+row+" both webSerial and barCodeSerial are specified, but they are inconsistent");
				}
				pid=webSerialToPid.get(row.getWebSerial());
			}
			row.setPid(pid);
			row.setBarcodeSerial(null);
			row.setWebSerial(null);
			bos.write(row.toString().getBytes());
		}
		
		bos.write("\t\t<print>".getBytes());
		bos.write("\t<database>".getBytes());
		bos.write("<xml>".getBytes());
		bos.close();
	}
*/	
	public String getAlphabet() {
		return alphabet;
	}

	public void setAlphabet(String alphabet) {
		this.alphabet = alphabet;
	}

	public String getPrintAuditCodes() {
		return printAuditCodes;
	}

	public void setPrintAuditCodes(String printAuditCodes) {
		this.printAuditCodes = printAuditCodes;
	}
}
