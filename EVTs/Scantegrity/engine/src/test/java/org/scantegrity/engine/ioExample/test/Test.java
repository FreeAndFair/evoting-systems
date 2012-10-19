package org.scantegrity.engine.ioExample.test;

import java.io.File;
import java.io.PrintStream;

import org.scantegrity.common.auditing.CheckBallotDecryption;
import org.scantegrity.common.auditing.CheckTableCorrectness;
import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;

import org.scantegrity.common.InputConstants;
import org.scantegrity.engine.MeetingFour;
import org.scantegrity.engine.MeetingOne;
import org.scantegrity.engine.MeetingThree;
import org.scantegrity.engine.MeetingTwo;
import org.scantegrity.engine.ioExample.MeetingFourIn;
import org.scantegrity.engine.ioExample.MeetingOneIn;
import org.scantegrity.engine.ioExample.MeetingThreeIn;
import org.scantegrity.engine.ioExample.MeetingTwoIn;

/**
 * Runs a full election: 4 meetings and 2 auditors
 * @author stefan
 *
 */
public class Test {
/*
	public boolean withAudit=false;

	PrintStream m1PrintStream=System.out;
	PrintStream m2PrintStream=System.out;
	PrintStream m3PrintStream=System.out;
	PrintStream m4PrintStream=System.out;
	PrintStream audit1PrintStream=System.out;
	PrintStream audit2PrintStream=System.out;
	
	public void testMeetingOne() throws Exception {
		String[] arg;
		long start=0;
		
		arg=new String[2];
		arg[0]=InputConstants.MeetingOneIn;		
		arg[1]=InputConstants.MeetingOneOut;
		
		//meeting one
		//create input
		MeetingOneIn.write(InputConstants.ElectionSpec,InputConstants.NoBallots,InputConstants.NoDs,InputConstants.C, InputConstants.Partitions, InputConstants.MeetingOneIn);
		//run meeting one
		start = System.currentTimeMillis();
		MeetingOne.main(arg);
		m1PrintStream.println("Meeting 1, NoBallots, "+InputConstants.NoBallots+", seconds, "+(System.currentTimeMillis()-start)/1000);				
	}
	
	public void testMeetingTwo() throws Exception {
		String[] arg;
		long start=0;
		
		//meeting two
		//Create Input
		MeetingTwoIn.write(InputConstants.PercentCheck,InputConstants.NoBallots,InputConstants.MeetingTwoIn);
		//run meeting two
		arg=new String[5];
		arg[0]=InputConstants.MeetingOneIn;
		arg[1]=InputConstants.MeetingTwoIn;
		arg[2]=InputConstants.MeetingTwoOut;
		arg[3]=InputConstants.MeetingTwoPrints;
		arg[4]=InputConstants.SerialMap;
		start = System.currentTimeMillis();
		MeetingTwo.main(arg);
		m2PrintStream.println("Meeting 2, NoBallots, "+InputConstants.NoBallots+", seconds, "+(System.currentTimeMillis()-start)/1000);
	}
	
	public void testMeetingThree() throws Exception {
		String[] arg;
		long start=0;
		
		//TODO check that the votes in are the votes out !!!
		//meeting three
		//create input
		MeetingThreeIn m3in=new MeetingThreeIn(InputConstants.MeetingOneIn);
		m3in.init(InputConstants.MK1,InputConstants.MK2);
		m3in.write(new ElectionSpecification(InputConstants.ElectionSpec),InputConstants.MeetingThreeIn,/*InputConstants.MeetingTwoPrints,*//*InputConstants.SerialMap);
		
		//run meeting three
		arg=new String[3];
		arg[0]=InputConstants.MeetingOneIn;
		arg[1]=InputConstants.MeetingThreeIn;
		arg[2]=InputConstants.MeetingThreeOut;
		start = System.currentTimeMillis();
		MeetingThree.main(arg);
		m3PrintStream.println("Meeting 3, NoBallots, "+InputConstants.NoBallots+", seconds, "+(System.currentTimeMillis()-start)/1000);				
	}
	public void testMeetingFour() throws Exception {
		String[] arg;
		long start=0;
		//meeting four
		//create input
		MeetingFourIn.write(InputConstants.MeetingThreeOut,InputConstants.MeetingFourIn);
		////run meeting four
		arg=new String[3];
		arg[0]=InputConstants.MeetingOneIn;
		arg[1]=InputConstants.MeetingFourIn;
		arg[2]=InputConstants.MeetingFourOut;
		start = System.currentTimeMillis();
		MeetingFour.main(arg);
		m4PrintStream.println("Meeting 4, NoBallots, "+InputConstants.NoBallots+", seconds, "+(System.currentTimeMillis()-start)/1000);		
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
		audit1PrintStream.println("audit one took "+(System.currentTimeMillis()-start)/1000+" seconds");		
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
		audit2PrintStream.println("audit two took "+(System.currentTimeMillis()-start)/1000+" seconds");
	}

	public void testAll() throws Exception {
		testMeetingOne();
		
		testMeetingTwo();
		
		//run the first audit
		if (withAudit) {
			testPreElectionAudit();
		}
				
		testMeetingThree();
		
		testMeetingFour();
		
		//run the second audit
		if (withAudit) {
			testPostElectionAudit();
		}		
	}
	
	public void increasingTheNumberOfBallots() throws Exception {
		m1PrintStream=new PrintStream(new File("MeetingOnePerFormance.csv"));
		m2PrintStream=new PrintStream(new File("MeetingTwoPerFormance.csv"));
		m3PrintStream=new PrintStream(new File("MeetingThreePerFormance.csv"));
		m4PrintStream=new PrintStream(new File("MeetingFourPerFormance.csv"));
		
		int MaxNoBallots=10000*38;
		int Step=1000*38;
		for (int noBallots=0;noBallots<=MaxNoBallots;noBallots+=Step) {
			InputConstants.NoBallots=noBallots;
			System.out.println("noBallots "+noBallots);
			testAll();
		}
		
		m1PrintStream.close();
		m2PrintStream.close();
		m3PrintStream.close();
		m4PrintStream.close();
	}
	*/
	public static void main(String[] args) throws Exception {
		//Test test=new Test();
		//test.increasingTheNumberOfBallots();
		//test.testAll();
		//InputConstants.setTempDir("Elections/POLK COUNTY, FLORIDA NOVEMBER 7, 2000/version4/bottom/");
		//test.testAll();
	}

}
