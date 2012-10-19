package org.scantegrity.engine.invisibleink;

import java.io.BufferedOutputStream;
import java.io.FileOutputStream;
import java.io.OutputStream;
import java.util.Set;


import org.bouncycastle.util.encoders.Base64;
import org.scantegrity.common.ballotstandards.basic.Question;
import org.w3c.dom.Document;

import org.scantegrity.authoring.invisibleink.ContestSymbols;
import org.scantegrity.common.BallotRow;
import org.scantegrity.common.InputConstants;
import org.scantegrity.common.InvisibleInkCodes;
import org.scantegrity.common.Prow;
import org.scantegrity.common.RowPermutation;
import org.scantegrity.common.Util;
import org.scantegrity.common.Commitments;

public class MeetingTwo extends org.scantegrity.engine.MeetingTwo {

	public MeetingTwo() throws Exception {
		super();
	}
	
	public MeetingTwo(String confFile) throws Exception {
		super(confFile);
	}

	public MeetingTwo(Document doc) throws Exception {
		super(doc);
	}
	
	public static void writeCodesToFile(String outputFile) throws Exception {
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

	public void makePrintsAndCommitmentsToCodes(String printOutputFile,String codeCommitmentsOutputFile) throws Exception {
		//eliminate the spoiled ballots
		Set<Integer> challenges=prows.keySet();
		int[] prints=new int[numberOfBallots-challenges.size()];
		int printsPos=0;
		
		for (int i=0;i<numberOfBallots;i++) {
			if (!challenges.contains(i))
				prints[printsPos++]=i;
		}
		
		ContestSymbols cs=new ContestSymbols(null,es,ContestSymbols.alphabet,true);
		
		BufferedOutputStream pos = new BufferedOutputStream(new FileOutputStream(printOutputFile));
		pos.write("<xml>\n".getBytes());
		pos.write("\t<database>\n".getBytes());
		pos.write("\t\t<codes>\n".getBytes());
			
		BufferedOutputStream cos = new BufferedOutputStream(new FileOutputStream(codeCommitmentsOutputFile));
		cos.write("<xml>\n".getBytes());
		cos.write("\t<database>\n".getBytes());
		cos.write("\t\t<printCommitments>\n".getBytes());

		InvisibleInkCodes invisibleInkCodes=new InvisibleInkCodes(es);
		invisibleInkCodes.init(mk1, mk2, c);
		Question[] qs=es.getOrderedQuestions();
		
		String serialPrefix=Util.getWardFromElectionConstant(new String(c));
		
		//generate the barcodes
		String[] barCodeSerials=RowPermutation.generateBarcodeSerialNumbers(mk1, mk2, c, serialPrefix, 100000, 999999, numberOfBallots);

		//generate the chit numbers
		String[] webSerials=RowPermutation.generateWebSerials(mk1, mk2, c, serialPrefix, 100000, 999999, numberOfBallots);
		
		//generate the two paswords for checking the printing
		String[] stubSerials=RowPermutation.generateStubSerials(serialPrefix, 1, numberOfBallots);
		//int[] passwords2=RowPermutation.generatePassword2(mk1, mk2, c, 100000, 999999, numberOfBallots);		
		
		//int chitSerial=-1;
		//int password1=-1;
		//int password2=-1;
		
		String barCodeSerialNumber=null;
		int ballotIndex=0;
		for (int pid:prints) {

			barCodeSerialNumber=barCodeSerials[pid];
			
			BallotRow ballotRow=new BallotRow();
			ballotRow.setWebSerial(webSerials[pid]+"");
			ballotRow.setBarcodeSerial(barCodeSerialNumber+"");
			ballotRow.setStubSerial(stubSerials[ballotIndex++]+"");
			//ballotRow.setPassword2(passwords2[pid]+"");
			
			pos.write(ballotRow.toString().getBytes());
			
			ballotRow.setPid(pid);
						
			//write the commitments to the chitserial and passwords
			//the barcode serial
			byte[] salt=Commitments.saltCode(mk1,mk2,this.c,(ballotRow.getPid()+" "+ballotRow.getBarcodeSerial()).getBytes()).getEncoded();
			byte[] commitment=Commitments.commitCode(
					salt, 
					this.c,
					//(ballotRow.getPid()+" "+ballotRow.getBarcodeSerial()).getBytes(),
					new byte[0],
					(ballotRow.getPid()+" "+ballotRow.getBarcodeSerial()).getBytes());
			ballotRow.setBarcodeSerialCommitment(commitment);
			
			//the chitserial
			salt=Commitments.saltCode(mk1,mk2,this.c,(ballotRow.getPid()+" "+ballotRow.getWebSerial()).getBytes()).getEncoded();
			commitment=Commitments.commitCode(
					salt, 
					this.c,
					//(ballotRow.getPid()+" "+ballotRow.getWebSerial()).getBytes(),
					new byte[0],
					(ballotRow.getPid()+" "+ballotRow.getWebSerial()).getBytes());
			ballotRow.setWebSerialCommitment(commitment);

			ballotRow.setStubSerial(null);
			ballotRow.setStubSerialSalt(null);
			ballotRow.setStubSerialCommitment(null);
			
			ballotRow.setBarcodeSerial(null);
			ballotRow.setBarcodeSerialSalt(null);
			
			ballotRow.setWebSerial(null);
			ballotRow.setWebSerialSalt(null);
			
			/*
			//password1
			salt=Commitments.saltCode(mk1,mk2,this.c,(ballotRow.getPid()+" "+ballotRow.getStubSerial()).getBytes()).getEncoded();
			commitment=Commitments.commitCode(
					salt, 
					this.c,(ballotRow.getPid()+" "+ballotRow.getStubSerial()).getBytes(), (ballotRow.getPid()+" "+ballotRow.getStubSerial()).getBytes());
			ballotRow.setStubSerialCommitment(commitment);
			
			
			//password2
			salt=Commitments.saltCode(mk1,mk2,this.c,(ballotRow.getPid()+" "+ballotRow.getPassword2()).getBytes()).getEncoded();
			commitment=Commitments.commitCode(
					salt, 
					this.c,(ballotRow.getPid()+" "+ballotRow.getPassword2()).getBytes(), (ballotRow.getPid()+" "+ballotRow.getPassword2()).getBytes());
			ballotRow.setPassword2Commitment(commitment);
			
			ballotRow.setBarcodeSerial(null);
			ballotRow.setWebSerial(null);
			ballotRow.setStubSerial(null);
			ballotRow.setPassword2(null);
			 */
			
			//write the xml
			cos.write(ballotRow.toString().getBytes());

			
			
			
			String[] nonPermutedCodes=invisibleInkCodes.getNonPermutedSymbols(pid);

			Prow p=new Prow();
			p.setId(pid);
			p.setChosenPage(Prow.ChosenPage.BOTH);
			computeP(p);
			
			String[] permutedCodes=cs.getAllSymbols(p, -1, nonPermutedCodes);


			int codeNumber=0;
			for (int q=0;q<qs.length;q++) {
				pos.write(("\t\t\t\t<question id=\""+q+"\">\n").getBytes());
				cos.write(("\t\t\t\t<question id=\""+q+"\">\n").getBytes());				
				for (int noCodesPerQuestion=0;noCodesPerQuestion<invisibleInkCodes.getNoCodesPerQuestion(qs[q]);codeNumber++,noCodesPerQuestion++) {
					String printCode=permutedCodes[codeNumber];
					String commitCode=nonPermutedCodes[codeNumber];
					
					if (printCode==null || commitCode==null) {
						Util.print(nonPermutedCodes);
						Util.print(permutedCodes);
						System.out.flush();
						throw new Exception("Got a null code");
					}
									
					pos.write(("\t\t\t\t\t<symbol id=\""+noCodesPerQuestion+"\" code=\""+printCode+"\"/>\n").getBytes());
					cos.write(("\t\t\t\t\t<symbol id=\""+noCodesPerQuestion+"\" c=\"").getBytes());
					
					int commitedCodeID=noCodesPerQuestion;
					
					salt=Commitments.saltCode(mk1,mk2,this.c,(pid+" "+q+" "+commitedCodeID).getBytes()).getEncoded();
					commitment=Commitments.commitCode(
							salt, 
							this.c,
							new byte[0],
							(pid+" "+q+" "+commitedCodeID+" "+commitCode).getBytes());

					cos.write(Base64.encode(commitment));
					cos.write("\"/>\n".getBytes());
				}
				pos.write(("\t\t\t\t</question>\n").getBytes());
				cos.write(("\t\t\t\t</question>\n").getBytes());
			}
			pos.write(BallotRow.getEndBallotTag().getBytes());
			cos.write(BallotRow.getEndBallotTag().getBytes());
		}
			
		cos.write("\t\t</printCommitments>\n".getBytes());
		cos.write("\t</database>\n".getBytes());
		cos.write("</xml>".getBytes());
		cos.close();
		
		pos.write("\t\t</codes>\n".getBytes());
		pos.write("\t</database>\n".getBytes());
		pos.write("</xml>".getBytes());
		pos.close();
	}

	
	public static void main(String[] args) throws Exception {
		MeetingTwo m2 = new MeetingTwo(args[0]);
		m2.init(InputConstants.MK1,InputConstants.MK2);		
		m2.go(args[1],args[2]);
		m2.makePrintsAndCommitmentsToCodes(args[3], args[7]);
		MeetingTwo.writeCodesToFile(args[6]);
	}

}
