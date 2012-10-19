package org.scantegrity.engine.invisibleink;

import org.scantegrity.common.auditing.CheckBallotDecryption;
import org.scantegrity.common.auditing.CheckCommitmentsToSymbols;
import org.scantegrity.common.auditing.CheckTableCorrectness;
import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;

import org.scantegrity.common.InputConstants;
import org.scantegrity.engine.MeetingOne;
import org.scantegrity.engine.ioExample.MeetingFourIn;
import org.scantegrity.engine.ioExample.MeetingOneIn;
import org.scantegrity.engine.ioExample.MeetingTwoIn;
import org.scantegrity.engine.scantegrity.MeetingThreeInScantegrity;

/**
 * Runs a full election: 4 meetings and 2 auditors
 * @author stefan
 *
 */
public class Test {

	public boolean withAudit=true;

	public void testCreateMeetingOneInput() throws Exception {
		//create input
		MeetingOneIn.write(InputConstants.ElectionSpec,InputConstants.NoBallots,InputConstants.NoDs,InputConstants.C, InputConstants.Partitions, InputConstants.MeetingOneIn);		
	}
	
	public void testMeetingOne() throws Exception {
		String[] arg;
		long start=0;
		
		arg=new String[3];
		arg[0]=InputConstants.MeetingOneIn;		
		arg[1]=InputConstants.MeetingOneOut;
		
		//meeting one
		//run meeting one
		start = System.currentTimeMillis();
		MeetingOne.main(arg);
		System.out.println("meting one took "+(System.currentTimeMillis()-start)/1000+" seconds");				
	}

	public void testCreatetMeetingTwoInput() throws Exception {
		//Create Input
				
		MeetingTwoIn.write(InputConstants.PercentCheck,InputConstants.NoBallots,InputConstants.MeetingTwoIn);		
	}
	
	public void testMeetingTwo() throws Exception {
		String[] arg;
		long start=0;
		
		//meeting two
		//run meeting two
		arg=new String[8];
		arg[0]=InputConstants.MeetingOneIn;
		arg[1]=InputConstants.MeetingTwoIn;
		arg[2]=InputConstants.MeetingTwoOut;
		arg[3]=InputConstants.MeetingTwoPrints;
		arg[5]=null;//InputConstants.SerialMap;
		arg[6]=InputConstants.Codes;
		arg[7]=InputConstants.MeetingTwoCodesCommitments;
		start = System.currentTimeMillis();
		MeetingTwo.main(arg);
		System.out.println("meting two took "+(System.currentTimeMillis()-start)/1000+" seconds");
		
	}

	public void testCreateRandomVotedBallots() throws Exception {
		//create input
		MeetingThreeInScantegrity m3in=new MeetingThreeInScantegrity(InputConstants.MeetingOneIn);
		m3in.init(InputConstants.MK1,InputConstants.MK2);
		m3in.write(new ElectionSpecification(InputConstants.ElectionSpec),InputConstants.MeetingTwoIn,InputConstants.BallotsDir);		
	}

	public void revealMarkedSymbols() throws Exception {
		long start=0;
		
		//run meeting three
		start = System.currentTimeMillis();
		MeetingThree m3=new MeetingThree(InputConstants.MeetingOneIn);
	
		m3.init(InputConstants.MK1,InputConstants.MK2);
		
		m3.clearVotesToCodedVotes(InputConstants.BallotsDir,InputConstants.MeetingThreeIn, null);		
		m3.revealMarkedSymbols(InputConstants.MeetingThreeIn, InputConstants.Codes, InputConstants.MeetingThreeOutCodes);		
		
		System.out.println("meting three took "+(System.currentTimeMillis()-start)/1000+" seconds");									
	}

	
	public void computeResults() throws Exception {
		long start=0;
		
		//run meeting three
		start = System.currentTimeMillis();
		MeetingThree m3=new MeetingThree(InputConstants.MeetingOneIn);
	
		m3.init(InputConstants.MK1,InputConstants.MK2);
		m3.go(InputConstants.MeetingThreeIn,InputConstants.MeetingThreeOut);		
	
		System.out.println("meting three took "+(System.currentTimeMillis()-start)/1000+" seconds");									
	}

	public void testCreateMeetingFourInput() throws Exception {
		MeetingFourIn.write(InputConstants.MeetingThreeOut,InputConstants.MeetingFourIn);		
	}
	
	public void testMeetingFour() throws Exception {
		String[] arg;
		long start=0;
		//meeting four
		//create input
		////run meeting four
		arg=new String[3];
		arg[0]=InputConstants.MeetingOneIn;
		arg[1]=InputConstants.MeetingFourIn;
		arg[2]=InputConstants.MeetingFourOut;
		start = System.currentTimeMillis();
		MeetingFour.main(arg);
		System.out.println("meting four took "+(System.currentTimeMillis()-start)/1000+" seconds");		
	}
	
	public void testPreElectionAudit() throws Exception {
		String[] arg;
		long start=0;

		arg=new String[4];
		arg[0]=InputConstants.MeetingOneIn;
		arg[1]=InputConstants.MeetingOneOut;
		arg[2]=InputConstants.MeetingTwoIn;
		arg[3]=InputConstants.MeetingTwoOut;
		start = System.currentTimeMillis();
		CheckTableCorrectness.main(arg);
		System.out.println("audit one took "+(System.currentTimeMillis()-start)/1000+" seconds");		
	}
	
	public void testAuditCodesForVotedCandidates() throws Exception {
		long start=0;
		/*
		 * 0 - m1in
		 * 1 - m2commit
		 * 2 - m3codes
		 * 3 - m3in
		 * 4 - serialmap
		*/
		String[] arg=new String[5];
		arg[0]=InputConstants.MeetingOneIn;
		arg[1]=InputConstants.MeetingTwoCodesCommitments;
		arg[2]=InputConstants.MeetingThreeOutCodes;
		arg[3]=InputConstants.MeetingThreeIn;

		start = System.currentTimeMillis();
		CheckCommitmentsToSymbols.main(arg);
		System.out.println("audit code commitments took "+(System.currentTimeMillis()-start)/1000+" seconds");		
	}

	public void testCodesCommitmentsSpoiledBallots() throws Exception {
		long start=0;
		/*
		 * 0 - m1in
		 * 1 - m2commit
		 * 2 - m3codes
		 * 3 - m3in
		 * 4 - serialmap
		*/
		String[] arg=new String[3];
		arg[0]=InputConstants.MeetingOneIn;
		arg[1]=InputConstants.MeetingTwoCodesCommitments;
		arg[2]=InputConstants.PrintAuditCodes;
		
		start = System.currentTimeMillis();
		CheckCommitmentsToSymbols.main(arg);
		System.out.println("audit code commitments took "+(System.currentTimeMillis()-start)/1000+" seconds");		
	}

	public void testCodesCommitmentsAllCodesOnCastBallots() throws Exception {
		long start=0;
		/*
		 * 0 - m1in
		 * 1 - m2commit
		 * 2 - m3codes
		 * 3 - m3in
		 * 4 - serialmap
		*/
		String[] arg=new String[5];
		arg[0]=InputConstants.MeetingOneIn;
		arg[1]=InputConstants.MeetingTwoCodesCommitments;
		arg[2]=InputConstants.ReplyToContestedBallots;
		arg[3]=InputConstants.MeetingThreeIn;
		start = System.currentTimeMillis();
		CheckCommitmentsToSymbols.main(arg);
		System.out.println("audit code commitments took "+(System.currentTimeMillis()-start)/1000+" seconds");		
	}

	
	public void testChallengedCodes() throws Exception {
		//run meeting three
		long start = System.currentTimeMillis();
		MeetingThree m3=new MeetingThree(InputConstants.MeetingOneIn);

		m3.init(InputConstants.MK1,InputConstants.MK2);
		m3.revealAllSymbolsOnVotedBallots(InputConstants.MeetingThreeIn, InputConstants.Codes, InputConstants.ReplyToContestedBallots);

		System.out.println("revealing all codes took "+(System.currentTimeMillis()-start)/1000+" seconds");				
	}

	public void testGenerateRandomSpoiledBallots() throws Exception {
		MeetingThreeInScantegrity m3in=new MeetingThreeInScantegrity(InputConstants.MeetingOneIn);
		m3in.init(InputConstants.MK1,InputConstants.MK2);
		m3in.write(new ElectionSpecification(InputConstants.ElectionSpec),InputConstants.MeetingTwoIn,InputConstants.SpoiledBallotsFromScanner);				
	}
	
	public void testRevealAuditedBallots() throws Exception {
		long start = System.currentTimeMillis();
		MeetingFour m4=new MeetingFour(InputConstants.MeetingOneIn);

		m4.init(InputConstants.MK1,InputConstants.MK2);
		m4.setAlphabet(InputConstants.Codes);
		m4.setPrintAuditCodes(InputConstants.PrintAuditCodes);

		String[] allM3InsAndM2In=new String[3];
		allM3InsAndM2In[0]=InputConstants.MeetingTwoIn;
		allM3InsAndM2In[1]=InputConstants.MeetingThreeIn;
		
		MeetingThree m3=new MeetingThree(InputConstants.MeetingOneIn);
		m3.init(InputConstants.MK1,InputConstants.MK2);		
		m3.clearVotesToCodedVotes(InputConstants.SpoiledBallotsFromScanner,InputConstants.SpoiledBallotsPid, null);		
		
		allM3InsAndM2In[2]=InputConstants.SpoiledBallotsPid;
		
		//InputConstants.Codes, InputConstants.PrintAuditCodes, 
		
		m4.revealUnvoted(allM3InsAndM2In, InputConstants.PrintAuditCodesMixnet);

		System.out.println("revealing all audited ballots took "+(System.currentTimeMillis()-start)/1000+" seconds");				
	}

	public void testCheckAuditedBallots() throws Exception {
		long start = System.currentTimeMillis();
		
		//check the codes
		testCodesCommitmentsSpoiledBallots();
		
		//check the mixnet
		String[] arg=new String[4];
		arg[0]=InputConstants.MeetingOneIn;
		arg[1]=InputConstants.MeetingOneOut;
		arg[2]=null;
		arg[3]=InputConstants.PrintAuditCodesMixnet;
		start = System.currentTimeMillis();
		CheckTableCorrectness.main(arg);

		
		System.out.println("checking all audited ballots took "+(System.currentTimeMillis()-start)/1000+" seconds");				
	}


	public void testPostElectionAudit() throws Exception {
		String[] arg;
		long start=0;

		arg=new String[6];
		arg[0]=InputConstants.MeetingOneIn;
		arg[1]=InputConstants.MeetingOneOut;
		arg[2]=InputConstants.MeetingThreeIn;
		arg[3]=InputConstants.MeetingThreeOut;
		arg[4]=InputConstants.MeetingFourIn;
		arg[5]=InputConstants.MeetingFourOut;
		start = System.currentTimeMillis();
		CheckBallotDecryption.main(arg);
		System.out.println("audit two took "+(System.currentTimeMillis()-start)/1000+" seconds");
	}

	public void testAll() throws Exception {

		testCreateMeetingOneInput();
		testMeetingOne();
		
		testCreatetMeetingTwoInput();
		testMeetingTwo();
				
		//run the first audit
		if (withAudit) {
			testPreElectionAudit();
		}
				
		testCreateRandomVotedBallots();

		revealMarkedSymbols();

		
		if (withAudit) {
			testAuditCodesForVotedCandidates();
		}
		
		testGenerateRandomSpoiledBallots();
		testRevealAuditedBallots();
		
		if (withAudit) {
			testCheckAuditedBallots();
		}
		
		computeResults();
		
		testCreateMeetingFourInput();
		
		testMeetingFour();
		
		//run the second audit
		if (withAudit) {
			testPostElectionAudit();
		}
		
		testChallengedCodes();
		
		if (withAudit) {
			testCodesCommitmentsAllCodesOnCastBallots();
		}
		
	}
	
	public static void main(String[] args) throws Exception {
		//Test test=new Test();
		//test.testAll();
	}

}
