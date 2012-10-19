package org.scantegrity.engine.invisibleink;

import java.io.BufferedOutputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Hashtable;
import java.util.TreeMap;

import org.bouncycastle.util.encoders.Base64;
import org.scantegrity.common.ballotstandards.Constants;
import org.scantegrity.common.ballotstandards.basic.Question;
import org.w3c.dom.Document;
import org.xml.sax.SAXException;

import org.scantegrity.common.BallotRow;
import org.scantegrity.common.Commitments;
import org.scantegrity.common.InvisibleInkCodes;
import org.scantegrity.common.Prow;
import org.scantegrity.common.RowPermutation;
import org.scantegrity.common.Util;

public class MeetingThree extends org.scantegrity.engine.scantegrity.MeetingThree {

	InvisibleInkCodes invisibleInkCodes=null;
	
	boolean revealAllSymbols=false;
	boolean revealBarcode=false;
	
	public MeetingThree(String confFile) throws Exception {
		super(confFile);
	}

	public MeetingThree(Document doc) throws Exception {
		super(doc);		
	}
	
	public MeetingThree() throws Exception {
		super();		
	}
	
	public void revealMarkedSymbols(String m3in,String pathToAlphabetFile, String outputFile) throws Exception {
		readPRows(m3in);
		revealAllSymbols=false;
		revealBarcode=false;
		revealSymbols(prows, pathToAlphabetFile, outputFile);		
	}

	public void revealAllSymbolsOnVotedBallots(String m3in,String pathToAlphabetFile, String outputFile) throws Exception {
		readPRows(m3in);
		revealAllSymbols=true;
		revealBarcode=false;
		revealSymbols(prows, pathToAlphabetFile, outputFile);
	}

	public void revealAllSymbolsOnSpoiledBallots(TreeMap<Integer,Prow> prows,String pathToAlphabetFile, String outputFile) throws Exception {
		revealAllSymbols=true;
		revealBarcode=true;
		revealSymbols(prows, pathToAlphabetFile, outputFile);
	}

	
	private void revealSymbols(TreeMap<Integer,Prow> prows,String pathToAlphabetFile, String outputFile) throws Exception {		
		InvisibleInkCodes.ReadCodes(pathToAlphabetFile);
		invisibleInkCodes=new InvisibleInkCodes(null,es);
		invisibleInkCodes.init(mk1, mk2, c);
				
		fos = new BufferedOutputStream(new FileOutputStream(outputFile));
		fos.write("<xml>\n".getBytes());
		fos.write("\t<database>\n".getBytes());
		fos.write("\t\t<printCommitments>\n".getBytes());
		
		String serialPrefix=Util.getWardFromElectionConstant(new String(c));
		
		//generate the barcode serial number
		String[] barCodeSerials=RowPermutation.generateBarcodeSerialNumbers(mk1, mk2, c, serialPrefix, 100000, 999999, numberOfBallots);
		
		//generate the chit numbers
		String[] webSerials=RowPermutation.generateWebSerials(mk1, mk2, c, serialPrefix, 100000, 999999, numberOfBallots);
		
		//generate the passwords
		//String[] passwords1=RowPermutation.generateStubSerials(serialPrefix, 1, numberOfBallots);
		//int[] passwords2=RowPermutation.generatePassword2(mk1, mk2, c, 100000, 999999, numberOfBallots);		

		String barCodeSerialNumber=null;		
		for (int pid:prows.keySet()) {
			barCodeSerialNumber=barCodeSerials[pid];
			
			BallotRow ballotRow=new BallotRow();
			ballotRow.setPid(pid);
			
			if (revealBarcode) {
				ballotRow.setBarcodeSerial(barCodeSerialNumber+"");
				ballotRow.setBarcodeSerialSalt(Commitments.saltCode(mk1,mk2,this.c,(ballotRow.getPid()+" "+ballotRow.getBarcodeSerial()).getBytes()).getEncoded());				
			}
			
			ballotRow.setWebSerial(webSerials[pid]+"");
			ballotRow.setWebSerialSalt(Commitments.saltCode(mk1,mk2,this.c,(ballotRow.getPid()+" "+ballotRow.getWebSerial()).getBytes()).getEncoded());			
			
			//ballotRow.setStubSerial(passwords1[pid]+"");
			//ballotRow.setStubSerialSalt(Commitments.saltCode(mk1,mk2,this.c,(ballotRow.getPid()+" "+ballotRow.getStubSerial()).getBytes()).getEncoded());

			/*
			ballotRow.setPassword2(passwords2[pid]+"");
			ballotRow.setPassword2Salt(Commitments.saltCode(mk1,mk2,this.c,(ballotRow.getPid()+" "+ballotRow.getPassword2()).getBytes()).getEncoded());
			*/
			
			fos.write(ballotRow.toString().getBytes());
			
			//all the Codes for this ballot
			String[] nonPermutedCodes=invisibleInkCodes.getNonPermutedSymbols(pid);

			//all the selections the voter made
			byte[] codedVotes=prows.get(pid).getVote();
			
			//project allSymbols on prowWithCodedVotes
			int noCodedVotesUntilcurrentQuestion=0;
			int nonPermutedCodesPos=0;
			Question[] qs=es.getOrderedQuestions();
			
			int noAnswersInCurrentQuestion=-1;
			
			for (int q=0;q<qs.length;q++) {
				fos.write(("\t\t\t\t<question id=\""+q+"\">\n").getBytes());
				//Arrays.sort(codedVotes,noCodedVotesUntilcurrentQuestion,qs[q].getMax());
				
				if (revealAllSymbols) {
					if (qs[q].getTypeOfAnswer().compareTo(Constants.RANK)!=0) {
						noAnswersInCurrentQuestion=qs[q].getAnswers().size();
					} else {
						noAnswersInCurrentQuestion=qs[q].getAnswers().size()*qs[q].getMax();
					}
				}
				else
					noAnswersInCurrentQuestion=qs[q].getMax();
				
				for (byte a=0;a<noAnswersInCurrentQuestion;a++) {
					byte currentCodedVote=-1;
					if (revealAllSymbols)
						currentCodedVote=a;
					else
						currentCodedVote=codedVotes[noCodedVotesUntilcurrentQuestion+a];
					
					if (currentCodedVote!=-1) {
						String code=nonPermutedCodes[nonPermutedCodesPos+currentCodedVote];
						if ( ! revealAllSymbols && 
								qs[q].getTypeOfAnswer().compareTo(Constants.RANK)==0) {
							code=nonPermutedCodes[nonPermutedCodesPos+currentCodedVote*qs[q].getMax()+a];
							currentCodedVote=(byte)(currentCodedVote*qs[q].getMax()+a);
						}
						
						fos.write(("\t\t\t\t\t<symbol id=\""+currentCodedVote+"\"" +
								" code=\""+code+"\""+
								" salt=\"").getBytes());
						byte[] salt=Commitments.saltCode(mk1,mk2,this.c,(pid+" "+q+" "+currentCodedVote).getBytes()).getEncoded(); 
						fos.write(Base64.encode(salt));
						fos.write("\"/>\n".getBytes());
					}
				}
				if (qs[q].getTypeOfAnswer().compareTo(Constants.RANK)!=0) {
					nonPermutedCodesPos+=qs[q].getAnswers().size();
				} else {
					nonPermutedCodesPos+=qs[q].getAnswers().size()*qs[q].getMax();
				}
				noCodedVotesUntilcurrentQuestion+=qs[q].getMax();
				fos.write(("\t\t\t\t</question>\n").getBytes());
			}
			fos.write(BallotRow.getEndBallotTag().getBytes());
		}

		fos.write("\t\t</printCommitments>\n".getBytes());
		fos.write("\t</database>\n".getBytes());
		fos.write("</xml>\n".getBytes());
		fos.close();	

		if (withSignatures)
			sign(outputFile);
		
	}
	
	protected void setSerialMap(String serialMap) throws SAXException, IOException {
		String[] barCodeSerials=null;
		try {
			//generate the barcode serial number
			barCodeSerials=RowPermutation.generateBarcodeSerialNumbers(mk1, mk2, c, "", 100000, 999999, numberOfBallots);
		} catch (Exception e) {
			e.printStackTrace();
		}
		serialToPid=new Hashtable<String,String>();
		for (int i=0;i<barCodeSerials.length;i++)
			serialToPid.put(barCodeSerials[i]+"", i+"");		
	}
}
