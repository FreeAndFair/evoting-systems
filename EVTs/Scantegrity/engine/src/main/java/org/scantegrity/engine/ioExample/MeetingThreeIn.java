package org.scantegrity.engine.ioExample;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;

import org.scantegrity.common.ballotstandards.GenerateDummyBallots;
import org.scantegrity.common.ballotstandards.Tally;
import org.scantegrity.common.ballotstandards.basic.Answer;
import org.scantegrity.common.ballotstandards.basic.Question;
import org.scantegrity.common.ballotstandards.basic.Section;
import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;
import org.scantegrity.common.ballotstandards.filledInBallot.FilledInBallot;
import org.scantegrity.common.ballotstandards.results.Results;
import org.w3c.dom.Document;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import java.util.Collections;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.Vector;

import org.scantegrity.common.InputConstants;
import org.scantegrity.common.Meeting;
import org.scantegrity.common.Prow;
import org.scantegrity.common.Util;

public class MeetingThreeIn extends Meeting { 
	
	public MeetingThreeIn() {
		super();
	}
	
	public MeetingThreeIn(String confFile) throws Exception {
		super(confFile);
	}

	public MeetingThreeIn(Document doc) throws Exception {
		super(doc);
	}
	
	public Hashtable<String,String> serialToPid=null; 
	
	public void ScannerOutputToMeetingThreeIn(String folderWithBallots,String m3in,String serialMap) throws Exception {
		setSerialMap(serialMap);
				
		OutputStream fos = new BufferedOutputStream(new FileOutputStream(m3in));
		fos.write("<xml>\n".getBytes());
		fos.write("\t<print>\n".getBytes());	
		
		ScannerOutputToMeetingThreeIn(folderWithBallots,fos);
		
		fos.write("\t</print>\n".getBytes());
		fos.write("</xml>".getBytes());
		fos.close();				
	}
	
	protected void setSerialMap(String serialMap) throws SAXException, IOException {
		serialToPid=Util.SerialToPid(serialMap);		
	}
	
	public void ScannerOutputToMeetingThreeIn(String folderWithBallots,OutputStream fos) throws Exception {
		File f=new File(folderWithBallots);
		if (f.isFile() && f.getName().endsWith(".enc")) {
			Document doc=Util.DomParse(f.getAbsolutePath());
			NodeList ballotNodes=doc.getElementsByTagName("row");
			
			for (int i=0;i<ballotNodes.getLength();i++) {
				Node ballotNode=ballotNodes.item(i);
				Prow prow=new Prow(ballotNode);			
				prow.setId(Integer.parseInt(serialToPid.get(prow.getId()+"")));			
				fos.write(prow.toString().getBytes());
			}			
		} else {
			if (f.isDirectory()) {
				File[] allFiles=f.listFiles();
				for (int i=0;i<allFiles.length;i++) {
					ScannerOutputToMeetingThreeIn(allFiles[i].getAbsolutePath(), fos);
				}
				return;
			}
		}

	}
	public Results write(ElectionSpecification es,String m3in,/*String m2Prints,*/String serialMap) throws Exception {
		
		//read the pid to serial mapping
		setSerialMap(serialMap);
		
		OutputStream fos = new BufferedOutputStream(new FileOutputStream(m3in));
		fos.write("<xml>\n".getBytes());
		fos.write("\t<print>\n".getBytes());	
		
		//transform from standard ballots to inputs to meeting three

        Prow.setOperation(Prow.Operation.NONE);
		
		GenerateDummyBallots gdb = new GenerateDummyBallots(es);

		//I need a hashtable that maps section Ids to ordered questions
		Hashtable<String, Question[]> sidToQs = new Hashtable<String, Question[]>();
		
		Tally tally = new Tally(es);
		Section[] ss = es.getOrderedSections();
		for (int i=0;i<ss.length;i++) {
			sidToQs.put(ss[i].getId(),ss[i].getOrderedQuestions());
		}

		Question[] qs = es.getOrderedQuestions();
		int maxNoAnswers = 0;
		for (int qno = 0; qno < qs.length; qno++) {			
			maxNoAnswers+=qs[qno].getMax();
		}
		
		Vector<Integer> printedBallots=new Vector<Integer>();
		if (serialToPid!=null)
			for (String serial:serialToPid.keySet()) {
				printedBallots.add(Integer.parseInt(serial));
			}
		else {
			for (int i=0;i<InputConstants.NoBallots*InputConstants.PercentVoted;i++) {
				printedBallots.add(i);
			}
		}
		Collections.shuffle(printedBallots);
		
		byte[] vote=new byte[maxNoAnswers];		
		for (int i=0;i<InputConstants.NoBallots*InputConstants.PercentVoted;i++) {
			
			Prow prow=new Prow();
			prow.setId(printedBallots.get(i));
			prow.setChosenPage(Prow.ChosenPage.BOTH);
			computeP(prow);			
			
			setChosenPage(prow);
						
			//read a filledInBallot and go through the questions
			FilledInBallot fib = gdb.generateOneBallot();
			
			
            //FileOutputStream fosfib = new FileOutputStream(i+".xml");
			//fosfib.write(fib.toString().getBytes());
			//fosfib.close();			
			
			
			tally.tally(fib);
			//go through each question
			int topPos = 0;
			int votePos=0;
			for (int s=0;s<ss.length;s++) {
				Question[] qsSpec = sidToQs.get(ss[s].getId());
				Section fibSection = (Section)fib.getSections().get(ss[s].getId());				
				for (int qpos = 0;qpos < qsSpec.length;qpos++) {
					Question fibQuestion = (Question)fibSection.getQuestions().get(qsSpec[qpos].getId());
					
					byte[] as = getAnswerPositions(fibQuestion.getAnswers());

					byte[] topInv = Util.getInverse(prow.getPage1(),topPos,qsSpec[qpos].getAnswers().size());
					byte[] bottomInv = Util.getInverse(prow.getPage2(),topPos,qsSpec[qpos].getAnswers().size());

					int previousVotePos=votePos;
					for (int apos = 0;apos<qsSpec[qpos].getMax();apos++) {
						try {
							vote[votePos++]=clearVoteToPunchScanVote(as[apos], topInv, bottomInv);
						} catch (ArrayIndexOutOfBoundsException e) {
							vote[--votePos]=-1;
						}
					}
					
					//permute the order of the answers a little
					int newPos=-1;
					byte temp=0;
					for (int j=previousVotePos;j<votePos;j++) {
						newPos=(int)(Math.random()*qsSpec[qpos].getMax());
						temp=vote[j];
						vote[j]=vote[previousVotePos+newPos];
						vote[previousVotePos+newPos]=temp;
					}
					
					topPos+=qsSpec[qpos].getAnswers().size();
				}
			}
			prow.setVote(vote);
			prow.setPage1(null);
			prow.setPage2(null);
			fos.write(("\t\t"+prow.toString()).getBytes());			
		}
		fos.write("\t</print>\n".getBytes());
		fos.write("</xml>".getBytes());
		fos.close();
		return tally.getResults();
	}

/*	
	public Results write(ElectionSpecification es,String m3in,String m2Prints,String serialMap) throws Exception {
		
		//read the pid to serial mapping
		setSerialMap(serialMap);
		
		OutputStream fos = new BufferedOutputStream(new FileOutputStream(m3in));
		fos.write("<xml>\n".getBytes());
		fos.write("\t<print>\n".getBytes());	
		
		//transform from standard ballots to inputs to meeting three
		//I need the file with the prints

		MeetingReaderSax mr = new MeetingReaderSax();
        try {
            SAXParser saxParser = Util.newSAXParser();
            saxParser.parse( new File(m2Prints), mr);
        } catch (Throwable t) {
            t.printStackTrace();
        }
        
        while (!mr.isDoneParsing()) {
        	Thread.sleep(100);
        }        

        Prow.setOperation(Prow.Operation.NONE);
		
		GenerateDummyBallots gdb = new GenerateDummyBallots(es);

		//I need a hashtable that maps section Ids to ordered questions
		Hashtable<String, Question[]> sidToQs = new Hashtable<String, Question[]>();
		
		Tally tally = new Tally(es);
		Section[] ss = es.getOrderedSections();
		for (int i=0;i<ss.length;i++) {
			sidToQs.put(ss[i].getId(),ss[i].getOrderedQuestions());
		}

		Question[] qs = es.getOrderedQuestions();
		int maxNoAnswers = 0;
		for (int qno = 0; qno < qs.length; qno++) {			
			maxNoAnswers+=qs[qno].getMax();
		}

		byte[] vote=new byte[maxNoAnswers];
		
		TreeMap<Integer, Prow> prows=mr.getProws();
		Vector<Integer> printedBallots=new Vector<Integer>();
		for (int serial:prows.keySet()) {
			printedBallots.add(serial);
		}
		Collections.shuffle(printedBallots);
		
		for (int i=0;i<InputConstants.NoBallots*InputConstants.PercentVoted-1;i++) {
			
			int serial=printedBallots.get(i);
			Prow prow=prows.get(serial);
			if (serialToPid!=null)
				prow.setId(Integer.parseInt(serialToPid.get(serial+"")));
			
			setPage(prow);
						
			//read a filledInBallot and go through the questions
			FilledInBallot fib = gdb.generateOneBallot();
			
			
            //FileOutputStream fosfib = new FileOutputStream("temp/before/"+i+".xml");
			//fosfib.write(fib.toString().getBytes());
			//fosfib.close();			
			
			
			tally.tally(fib);
			//go through each question
			int topPos = 0;
			int votePos=0;
			for (int s=0;s<ss.length;s++) {
				Question[] qsSpec = sidToQs.get(ss[s].getId());
				Section fibSection = (Section)fib.getSections().get(ss[s].getId());				
				for (int qpos = 0;qpos < qsSpec.length;qpos++) {
					Question fibQuestion = (Question)fibSection.getQuestions().get(qsSpec[qpos].getId());
					
					byte[] as = getAnswerPositions(fibQuestion.getAnswers());

					byte[] topInv = Util.getInverse(prow.getPage1(),topPos,qsSpec[qpos].getAnswers().size());
					byte[] bottomInv = Util.getInverse(prow.getPage2(),topPos,qsSpec[qpos].getAnswers().size());

					for (int apos = 0;apos<qsSpec[qpos].getMax();apos++) {
						try {
							vote[votePos++]=ClearVoteToPunchScanVote(as[apos], topInv, bottomInv);
						} catch (ArrayIndexOutOfBoundsException e) {
							vote[--votePos]=-1;
						}
					}
					
					topPos+=qsSpec[qpos].getAnswers().size();
				}
			}
			prow.setVote(vote);
			prow.setPage1(null);
			prow.setPage2(null);
			fos.write(("\t\t"+prow.toString()).getBytes());			
		}
		fos.write("\t</print>\n".getBytes());
		fos.write("</xml>".getBytes());
		fos.close();
		return tally.getResults();
	}
*/	
	protected byte[] getAnswerPositions(Hashtable fibAnswers) {
		byte[] ret = new byte[fibAnswers.size()];
		int pos = 0;
		for (Iterator i = fibAnswers.values().iterator();i.hasNext();) {
			Answer a = (Answer)i.next();
			ret[pos]=(byte)(a.getPossition()-1);//(byte)(Byte.parseByte(((Answer)esAnswers.get(a.getId())).getId())-1);
			pos++;
		}
		return ret;
	}

	public byte clearVoteToPunchScanVote(byte vote, byte[] topInv, byte[] bottomInv) {
		return bottomInv[topInv[vote]];		
	}

	public void setChosenPage(Prow prow) {
		if (Math.random()<0.5)
			prow.setChosenPage(Prow.ChosenPage.TOP);
		else
			prow.setChosenPage(Prow.ChosenPage.BOTTOM);		
	}
	
	public static int[] GenerateRandomPermutation(int size) {
		int[] ret=new int[size];
		for (int i=0;i<ret.length;i++)
			ret[i]=i;
		int newPos=-1;
		int temp=0;
		for (int i=0;i<ret.length;i++) {
			newPos=(int)(Math.random()*ret.length);
			temp=ret[i];
			ret[i]=ret[newPos];
			ret[newPos]=temp;
		}
		return ret;
	}
	
	public static void main(String args[]) throws Exception {
		String dir="Elections/VoComp/";
		MeetingThreeIn m3in=new MeetingThreeIn();
		m3in.ScannerOutputToMeetingThreeIn(dir+"PunchScan/ballots/", dir+"MeetingThreeIn.xml",dir+"SerialMap.xml");
	}
}
