/*
 * Scantegrity - Successor to Punchscan, a High Integrity Voting System
 * Copyright (C) 2006  Richard Carback, David Chaum, Jeremy Clark, 
 * Aleks Essex, Stefan Popoveniuc, and Jeremy Robin
 * 
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */

package org.scantegrity.common;

public class InputConstants {
	public static enum BallotType {PUNCHSCAN,SCANTEGRITY,SCANTEGRITY_II,NONE}
	
	
	public static BallotType FrontEnd=BallotType.SCANTEGRITY_II;	

	public static byte[] MK1 = "G7S-)bj^l;q1800]".getBytes();
	public static byte[] MK2 = "K*dst>p9H6c38?[!".getBytes();
	public static byte[] C = "LinuxUsersGroup ".getBytes();		
	
	public static int NoBallots = 100;
	public static int NoDs = 4;
	public static double PercentCheck = 0.5;
	public static double PercentVoted = 0.2;///38f;//0.5;
	public static int PrintBatchSize = 100;
	
	public static int Dpi = 150;
	public static int NoCols = 1;
	
	//public static String folder="D:/PunchScan2.0/PunchScan2.0/Elections/TP Nov 3 2009, mock PUBLIC/";
	//public static String folder="D:/PunchScan2.0/PunchScan2.0/Elections/BenDemo/";
	public static String folder="PUBLIC/";
	
	public static String privateFolder = folder+"private/";	
	public static String publicFolder = folder;//+"public/";
		
	public static String ElectionSpec = publicFolder+"ElectionSpec.xml";
	public static String Partitions = publicFolder+"partitions.xml";
	
	public static String MeetingOneIn = publicFolder+"MeetingOneIn.xml";
	public static String MeetingTwoIn = publicFolder+"MeetingTwoIn.xml";
	public static String MeetingThreeIn = publicFolder+"MeetingThreeIn.xml";
	public static String MeetingFourIn = publicFolder+"MeetingFourIn.xml";
	
	public static String MeetingOneOut = publicFolder+"MeetingOneOut.xml";
	public static String MeetingTwoOut = publicFolder+"MeetingTwoOut.xml";
	public static String MeetingThreeOut = publicFolder+"MeetingThreeOut.xml";
	public static String MeetingThreeOutCodes = publicFolder+"MeetingThreeOutCodes.xml";
	public static String MeetingFourOut = publicFolder+"MeetingFourOut.xml";
	public static String MeetingThreeAndAHalfOut = publicFolder+"MeetingThreeAndAHalfOut.xml";
	
	public static String MeetingTwoPrints = privateFolder+"MeetingTwoPrints.xml";
	
	public static String Codes = publicFolder+"PrintCodes.xml";
	public static String MeetingTwoCodesCommitments = publicFolder+"MeetingTwoOutCommitments.xml";	
	public static String SerialMap = publicFolder+"SerialMap.xml";
	
//	public static String ClearTextBallots=privateFolder+"ballots/";//.xml";
	
	public static String ContestedCodes = publicFolder+"ContestedCodes.xml";
	public static String ReplyToContestedBallots = publicFolder+"ReplyToContestedCodes.xml";
	public static String BallotsToBeRetrievedFromTheWarehouse = publicFolder+"BallotsToBeRetrievedFromTheWarehouse.xml";
	
	public static String SpoiledBallotsFromScanner=publicFolder+"SpoiledBallotsFromScanner.xml";
	public static String SpoiledBallotsPid=publicFolder+"SpoiledBallotsPid.xml";
	
	public static String PrintAuditCodes=publicFolder+"PrintAuditCodes.xml";
	public static String PrintAuditCodesMixnet =publicFolder+"PrintAuditMixnet.xml";
	
	public static String Geometry = publicFolder+"geometry.xml";
	public static String PdfTemplate = publicFolder+"background.pdf";
	
	public static String JavaCreatedForm = publicFolder+"javaCreatedForm.pdf";
	
	public static String PdfFormsDir = publicFolder+"pdfBallots/";	
	
	public static String BallotsDir = privateFolder+"ballots";
	public static String BallotsBackupDir = privateFolder+"backup";
	public static String ScannesDir = privateFolder+"scannes";
	public static String WriteinsDir = privateFolder+"write-ins";
	
	public static void setFolder(String tempDir) {
		folder=tempDir;
		
		setPublicFolder(folder+"public/");	
		setPrivateFolder(folder+"private/");
	}
	
	public static void setPublicFolder(String tempDir) {	
		publicFolder = tempDir;
			
		ElectionSpec = publicFolder+"ElectionSpec.xml";
		Partitions = publicFolder+"partitions.xml";
		
		MeetingOneIn = publicFolder+"MeetingOneIn.xml";
		MeetingTwoIn = publicFolder+"MeetingTwoIn.xml";
		MeetingThreeIn = publicFolder+"MeetingThreeIn.xml";
		MeetingFourIn = publicFolder+"MeetingFourIn.xml";
		
		MeetingOneOut = publicFolder+"MeetingOneOut.xml";
		MeetingTwoOut = publicFolder+"MeetingTwoOut.xml";
		MeetingThreeOut = publicFolder+"MeetingThreeOut.xml";
		MeetingThreeOutCodes = publicFolder+"MeetingThreeOutCodes.xml";
		MeetingFourOut = publicFolder+"MeetingFourOut.xml";
		MeetingThreeAndAHalfOut = publicFolder+"MeetingThreeAndAHalfOut.xml";
		
		
		Codes = publicFolder+"PrintCodes.xml";
		MeetingTwoCodesCommitments = publicFolder+"MeetingTwoOutCommitments.xml";	
		SerialMap = publicFolder+"SerialMap.xml";
		
		ContestedCodes = publicFolder+"ContestedCodes.xml";
		ReplyToContestedBallots = publicFolder+"ReplyToContestedCodes.xml";
		BallotsToBeRetrievedFromTheWarehouse = publicFolder+"BallotsToBeRetrievedFromTheWarehouse.xml";
		
		PrintAuditCodes=publicFolder+"PrintAuditBallots.xml";
		PrintAuditCodesMixnet =publicFolder+"PrintAuditMixnet.xml";
		
		SpoiledBallotsFromScanner=publicFolder+"SpoiledBallotsFromScanner.xml";
		SpoiledBallotsPid=publicFolder+"SpoiledBallotsPid.xml";
		
		Geometry = publicFolder+"geometry.xml";
		PdfTemplate = publicFolder+"background.pdf";
	}	
	
	public static void setPrivateFolder(String tempDir) {
		privateFolder = tempDir;	
					
		MeetingTwoPrints = privateFolder+"MeetingTwoPrints.xml";

		BallotsDir = privateFolder+"ballots";
		
		BallotsBackupDir = privateFolder+"backup";
		ScannesDir = privateFolder+"scannes";
		WriteinsDir = privateFolder+"write-ins";
		
//		ClearTextBallots=privateFolder+"ballots.xml";		
	}	

}
