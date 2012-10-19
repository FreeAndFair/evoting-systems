package org.scantegrity.common.auditing;

import java.io.File;
import java.io.IOException;
import java.util.Iterator;
import java.util.TreeMap;

import javax.xml.parsers.SAXParser;

import org.scantegrity.common.auditing.ParseM2CodesCheckCommitments;
import org.scantegrity.common.BallotRow;
import org.scantegrity.common.CodesReaderSax;
import org.scantegrity.common.Meeting;
import org.scantegrity.common.MeetingReaderSax;
import org.scantegrity.common.Prow;
import org.scantegrity.common.SymbolRow;
import org.scantegrity.common.Util;
import org.scantegrity.common.ballotstandards.Constants;
import org.scantegrity.common.ballotstandards.basic.Question;
import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;


public class CheckCommitmentsToSymbols {

	//printedSerial, question, symbol
	TreeMap<Integer,TreeMap<Byte,TreeMap<Byte,SymbolRow>>> rows=new TreeMap<Integer, TreeMap<Byte,TreeMap<Byte,SymbolRow>>>();
	
	//the various serial numbers - 2D barcode, chit serial and 2 passwords on the chit
	TreeMap<Integer,BallotRow> serials=null;
	
	byte[] c;
	ElectionSpecification es=null;
	
	//read in memory m3outcodes
	public CheckCommitmentsToSymbols(String meetingThreeOutCodes,String m1in) throws Exception {

		Meeting m=new Meeting(m1in);
		c=m.getC();
		es=m.getEs();
		
		//read MeetingThreeOutCodes.xml
		CodesReaderSax cr = new CodesReaderSax();
        SAXParser saxParser = Util.newSAXParser();
        if (meetingThreeOutCodes!=null && meetingThreeOutCodes.length()!=0) {
	        saxParser.parse( new File(meetingThreeOutCodes), cr);
	        while (!cr.isDoneParsing()) {
	        	Thread.sleep(100);
	        }
        }
        rows=cr.getRows();        
        serials = cr.getSerials();
	}
	
	public void check(String m2outCodesComm,String m3in) throws SAXException, IOException, InterruptedException {
        checkCommitments(m2outCodesComm);
        
        checkM3CodesisM3In(m3in);
	}

	public void checkCommitments(String m2outCodesComm) throws SAXException, IOException {
        DefaultHandler handler = new ParseM2CodesCheckCommitments(rows,serials,c);
        SAXParser saxParser = Util.newSAXParser();
        saxParser.parse( new File(m2outCodesComm), handler);		
	}
	
	public void checkM3CodesisM3In(String m3in) throws SAXException, IOException, InterruptedException {
		
		//read m3in in memory
		MeetingReaderSax mr = new MeetingReaderSax();
        SAXParser saxParser = Util.newSAXParser();
        saxParser.parse( new File(m3in), mr);
        
        while (!mr.isDoneParsing()) {
        	Thread.sleep(100);
        }        
		TreeMap<Integer,Prow> m3inProws=mr.getProws();
		
		Question[] qs=es.getOrderedQuestions();
		
		//go through all the ballots in m3in
		for (Iterator<Prow> it=m3inProws.values().iterator();it.hasNext();) {
			Prow prow=it.next();
			
			TreeMap<Byte,TreeMap<Byte,SymbolRow>> ballot=rows.get(prow.getId());
			if (ballot==null)
				throw new SAXException("Ballot with pid="+prow.getId()+" (printedSerial="+prow.getId()+") does not have the codes revealed. ");
			byte[] vote=prow.getVote();
			int votepos=0;
			for (Question q:qs) {
				TreeMap<Byte,SymbolRow> qm3Codes=ballot.get(Byte.parseByte(q.getId()));
				if (qm3Codes==null)
					throw new SAXException("For ballot with pid="+prow.getId()+" (printedSerial="+prow.getId()+") question="+q.getId()+" the codes are not revealed.");
				for (int a=0;a<q.getMax();a++) {
					if (vote[votepos]!=-1) {
						byte codedCandidate=vote[votepos];
						if (q.getTypeOfAnswer().equals(Constants.RANK))
							codedCandidate=(byte)(codedCandidate * q.getMax()+a);
						if (qm3Codes.get(codedCandidate)==null) {
							throw new SAXException("For ballot with pid="+prow.getId()+" (printedSerial="+prow.getId()+") question="+q.getId()+" codedVote="+codedCandidate+" the code is not revealed.");
						}
					}
					votepos++;
				}
			}
		}
	}
	
	/*
	 * 0 - m1in
	 * 1 - m2commit
	 * 2 - m3codes
	 * 3 - m3in
	 * 4 - serialmap
	 */
	public static void main(String[] args) throws Exception {
		CheckCommitmentsToSymbols ccts=new CheckCommitmentsToSymbols(args[2],args[0]);
		if (args.length>3)
			ccts.check(args[1],args[3]);
		else
			ccts.checkCommitments(args[1]);
	}
}
