package org.scantegrity.common.auditing;

import java.io.File;
import java.util.Iterator;
import java.util.TreeMap;

import javax.xml.parsers.SAXParser;

import org.xml.sax.helpers.DefaultHandler;

import org.scantegrity.common.auditing.ParseMeetingOneOutCBD;
import org.scantegrity.common.Drow;
import org.scantegrity.common.Drow.ChosenSide;
import org.scantegrity.common.InputConstants;
import org.scantegrity.common.MarkPermutations;
import org.scantegrity.common.Meeting;
import org.scantegrity.common.MeetingReaderSax;
import org.scantegrity.common.Prow;
import org.scantegrity.common.Rrow;
import org.scantegrity.common.Util;

/**
 * checks:
 * - all the voted balots have been transformed
 * - all the challenges have been opened on the correct side
 * - ballots were properly printed (commitments for the revealed page)
 * - ballots were properly transformed (from P3 to D3 or from D3 to R)
 * - commitments to D2 or D4 is valid
 * 
 * algorithm:
 * - read in memory MeetingOneIn.xml (constant and ElectionSpecification)
 * - read in memory MeetingThreeIn.xml
 * 		- optional [check that the ballots that use for voting are not in MeetingTwoOut.xml]
 * - read in memory MeetingThreeOut.xml
 * - read in memory MeetingFourIn.xml
 * 		- optional [check that each challenge is for a valid did (is also in MeetingThreeOut.xml)]
 * - read in memory MeetingFourOut.xml
 *		- check that all the requests have been opened on the correct side
 * 		- check that all the transformation have been made corectly
 * - go through each line of MeetingOneOut.xml (use sax)
 * 		- if a row in P is found, check if it is MeetingThreeOut
 * 			- check the commitment for p1 or p2
 * 		- if a row in D in found
 * 			- check the commeiment for d2 or d4
 */
public class CheckBallotDecryption {
	
	byte[] c=null;
	MarkPermutations markPerm=null;
	private TreeMap<Integer,Prow> m3inProws;
	private TreeMap<Integer, Prow> m3outProws;
	private TreeMap<Byte, TreeMap<Byte, TreeMap<Integer, Drow>>> m3outDrows;
	private TreeMap<Byte, TreeMap<Byte, TreeMap<Integer, Drow>>> m4inDRows;
	private TreeMap<Byte, TreeMap<Byte, TreeMap<Integer, Drow>>> m4outDrows;
	private TreeMap<Byte,TreeMap<Integer, Rrow>> m3outRrows;
	
	/**
	 * parses the five parameters and puts them into memory.
	 * 
	 * They are smaller them m1out (m1out will not be kept in memory)
	 * 
	 * @param meetingOneIn
	 * @param meetingThreeIn
	 * @param meetingThreeOut
	 * @param meetingFourIn
	 * @param meetingFourOut
	 * @throws Exception
	 */
	public CheckBallotDecryption(String meetingOneIn,String meetingThreeIn, String meetingThreeOut, String meetingFourIn,String meetingFourOut) throws Exception {
		//read meetingOneIn
		Meeting m=new Meeting(meetingOneIn);
		c=m.getC();
		markPerm=new MarkPermutations(c,m.getEs(),m.getPartitions());
		
		//read meetingThreeIn
		MeetingReaderSax mr = new MeetingReaderSax();
        SAXParser saxParser = Util.newSAXParser();
        saxParser.parse( new File(meetingThreeIn), mr);
        
        while (!mr.isDoneParsing()) {
        	Thread.sleep(100);
        }        
		m3inProws=mr.getProws();
	
		//read meetingThreeOut
		mr = new MeetingReaderSax();
        saxParser = Util.newSAXParser();
        saxParser.parse( new File(meetingThreeOut), mr);

        while (!mr.isDoneParsing()) {
        	Thread.sleep(100);
        }
		m3outProws=mr.getProws();
		m3outDrows=mr.getDrows();
		m3outRrows=mr.getRrows();
		
		//read meetingFourIn
		mr = new MeetingReaderSax();
		saxParser = Util.newSAXParser();
        saxParser.parse( new File(meetingFourIn), mr);

        while (!mr.isDoneParsing()) {
        	Thread.sleep(100);
        }
		m4inDRows=mr.getDrows();
		
		//read meetingFourOut
		mr = new MeetingReaderSax();
		saxParser = Util.newSAXParser();
        saxParser.parse( new File(meetingFourOut), mr);

        while (!mr.isDoneParsing()) {
        	Thread.sleep(100);
        }
		m4outDrows=mr.getDrows();
	}
	
	/**
	 * First checks the transformations (d3=p3+d2 or r=d3+d4). Then
	 * it checks the commitments
	 * 
	 * All the challenges have to be checked. m1in is not read in memory
	 * @param meetingOneout
	 * @throws Exception - if the auditor find an iregularity, or (null) 
	 * if one of the challenges is not opened
	 */
	public void check(String meetingOneout) throws Exception {
		checkTransformations();
		
		//check the commitments
        DefaultHandler handler = new ParseMeetingOneOutCBD(m3inProws,m3outProws,m4inDRows,m4outDrows,c);
        SAXParser saxParser = Util.newSAXParser();
        saxParser.parse( new File(meetingOneout), handler);
	}
/*
	private void checkTransformations() throws Exception {
		for (byte partitionId:m3outDrows.keySet()) {
			TreeMap<Byte,TreeMap<Integer,Drow>> i=m3outDrows.get(partitionId);
			for (byte dNo:i.keySet()) {
				TreeMap<Integer,Drow> j=i.get(dNo);
				for (Iterator<Drow> k=j.values().iterator();k.hasNext();) {
					Drow m3outDrow=k.next();
					Drow m4outDrow=m4outDrows.get(partitionId).get(dNo).get(m3outDrow.getId());
					if (m4inDRows.get(partitionId).get(dNo).get(m3outDrow.getId()).getChosenSide().equals(ChosenSide.LEFT)) {
						//compose p3 with d2 to get d3
						byte[] p3=m3inProws.get(m4outDrow.getPid()).getVote();
						//try {} catch (NullPointerException e) {throw new Exception("p3 missing dInstance="+dNo+" did="+drow.getId());}
						byte[] d2=m4outDrow.getPage1();
						byte[] d3=markPerm.computeD3(p3, d2, partitionId);
						if (Util.compare(d3,m3outDrow.getVote())!=0)
							throw new Exception("p3+d2!=d3 for partition="+partitionId+" dInstance="+dNo+" did="+m3outDrow.getId());						
					}
					if (m4inDRows.get(partitionId).get(dNo).get(m3outDrow.getId()).getChosenSide().equals(ChosenSide.RIGHT)) {
						//compose d3 with d4 to get r
						byte[] d3=m3outDrow.getVote();
						byte[] d4=m4outDrow.getPage2();
						byte[] rreconstructed=markPerm.computeR(d3, d4, partitionId);
						byte[] rGiven=m3outRrows.get(partitionId).get(m4outDrow.getRid()).getVote();
						if (Util.compare(rreconstructed, rGiven)!=0){
							Util.print(d3);
							Util.print(d4);
							Util.print(rreconstructed);
							Util.print(rGiven);
							throw new Exception("d3+d4!=r for partition="+partitionId+" dInstance="+dNo+" did="+m3outDrow.getId());
						}
					}
				}
			}
		}
	}
*/
	
	private void checkTransformations() throws Exception {
		for (byte partitionId:m4inDRows.keySet()) {
			TreeMap<Byte,TreeMap<Integer,Drow>> partition=m4inDRows.get(partitionId);
			if (partition==null)
				throw new Exception("Invalid partition |"+partitionId+"|in m4in");
			for (byte dNo:partition.keySet()) {
				TreeMap<Integer,Drow> dTable=partition.get(dNo);
				if (dTable==null)
					throw new Exception("Invalid dtable |"+dNo+"| in partition |"+partitionId+"|in m4in");				
				for (Iterator<Drow> k=dTable.values().iterator();k.hasNext();) {
					Drow m4inDrow=k.next();
					Drow m3outDrow=m3outDrows.get(partitionId).get(dNo).get(m4inDrow.getId());
					if (m3outDrow==null)
						throw new Exception("Invalid chalenge |"+m4inDrow.getId()+"| in dtable |"+dNo+"| in partition |"+partitionId+"|in m4in");									
					Drow m4outDrow=m4outDrows.get(partitionId).get(dNo).get(m3outDrow.getId());
					if (m4outDrow==null)
						throw new Exception("chalenge |"+m4inDrow.getId()+"| in dtable |"+dNo+"| in partition |"+partitionId+"|in m4in was not responded to");														
					if (m4inDrow.getChosenSide().equals(ChosenSide.LEFT)) {
						byte[] p3=null;
						try {
							p3=m3inProws.get(m4outDrow.getPid()).getVote();
						} catch (NullPointerException e) {
							//keep p3 null
						}
						if (p3==null)
							throw new Exception("p3 wrong in partition="+partitionId+" dInstance="+dNo+" did="+m4outDrow.getId());
						byte[] d2=m4outDrow.getPage1();
						byte[] d3=markPerm.computeD3(p3, d2, partitionId);
						//compose p3 with d2 to get d3
						if (Util.compare(d3,m3outDrow.getVote())!=0)
							throw new Exception("p3+d2!=d3 for partition="+partitionId+" dInstance="+dNo+" did="+m3outDrow.getId());						
					}
					if (m4inDrow.getChosenSide().equals(ChosenSide.RIGHT)) {
						byte[] rGiven=null;
						try {
							rGiven=m3outRrows.get(partitionId).get(m4outDrow.getRid()).getVote();
						} catch (NullPointerException e) {
							//keep rGiven null
						}
						if (rGiven==null)
							throw new Exception("rid wrong in partition="+partitionId+" dInstance="+dNo+" did="+m4outDrow.getId());

						//compose d3 with d4 to get r
						byte[] d3=m3outDrow.getVote();
						byte[] d4=m4outDrow.getPage2();
						byte[] rreconstructed=markPerm.computeR(d3, d4, partitionId);
						
						if (Util.compare(rreconstructed, rGiven)!=0){
							Util.print(d3);
							Util.print(d4);
							Util.print(rreconstructed);
							Util.print(rGiven);
							throw new Exception("d3+d4!=r for partition="+partitionId+" dInstance="+dNo+" did="+m3outDrow.getId());
						}
					}
				}
			}
		}
	}

	
	/**
	 * Debug method
	 * @param args
	 * @throws Exception
	 */
	public static void main(String[] args) throws Exception {
		CheckBallotDecryption cbd=new CheckBallotDecryption(InputConstants.MeetingOneIn,InputConstants.MeetingThreeIn,InputConstants.MeetingThreeOut,InputConstants.MeetingFourIn,InputConstants.MeetingFourOut);
		cbd.check(InputConstants.MeetingOneOut);
	}	
	
}
