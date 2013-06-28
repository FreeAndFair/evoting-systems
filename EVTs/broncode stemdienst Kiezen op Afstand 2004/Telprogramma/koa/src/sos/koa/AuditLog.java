/*
 * JML specification Copyright 2004 SoS Group, University of Nijmegen
 */

package sos.koa;

import javax.xml.transform.Source;
import javax.xml.transform.sax.SAXSource;
import java.util.Date;
import java.util.TreeMap;
import javax.print.attribute.DateTimeSyntax;

/**
 * This class is used to store all the information needed to
 * generate the 'Verwerkingsverslag' report. In addition it is
 * also used to store information needed for the 'Resultaat van de
 * stemming' report.
 *
 * @version $Id: AuditLog.java,v 1.24 2004/05/28 20:37:22 hubbers Exp $
 *
 * @author Engelbert Hubbers (hubbers@cs.kun.nl)
 */

public class AuditLog 
{
 // General section...
 /** The creation time of the audit log. */
 /*@ spec_public @*/ private static String logTimestamp;

 /** The string that contains the voting interval. */
 /*@ spec_public @*/ private static String votingInterval;

 /** Flag indicating whether the number of registered voters has been set
  *  or not. Important for some invariants
  */ 
 /*@ spec_public @*/ private static boolean votingNrOfRegisteredVotersSet = false;
 //@ constraint \old(votingNrOfRegisteredVotersSet) ==> votingNrOfRegisteredVotersSet;

 /** The number of registered voters. We assume this non-negative number is
  *  greater or equal to the imported nr of votes from the 'stembus export'.
  */
 /*@ spec_public @*/ private static int votingNrOfRegisteredVoters = 0;
 //@ invariant votingNrOfRegisteredVotersSet ==> votingNrOfRegisteredVoters >= importVotesNrOfVotes;
 //@ invariant votingNrOfRegisteredVotersSet ==> votingNrOfRegisteredVoters >= decryptNrOfVotes;
 //@ invariant votingNrOfRegisteredVotersSet ==> votingNrOfRegisteredVoters >= countNrOfVotes;
 //@ invariant votingNrOfRegisteredVoters >= 0;

 /** The string that contains the name of the voting bureau. */
 /*@ spec_public @*/ private static String votingBureau;

 /** The string that contains the name of the voting chairman. */
 /*@ spec_public @*/ private static String votingChairman;

 /** The string that contains the state of the voting. */
 /*@ spec_public @*/ private static String votingState;

 /** The string that contains the name of the election. */
 /*@ spec_public @*/ private static String votingElection;

 /** The string that contains the starting time of the election. */
 /*@ spec_public @*/ private static String votingElectionTimestampStart;

 /** The string that contains the ending time of the election. */
 /*@ spec_public @*/ private static String votingElectionTimestampEnd;

 /** The string that contains the timestamp for the export of the votes. */
 /*@ spec_public @*/ private static String votingExportTimestamp;

 /** The TreeMap that is used to store the kiesKringen found in the
  * file with the votes.
  */
 private static /*@ spec_public non_null @*/ TreeMap kiesKringen = new TreeMap(); 
 //@ invariant kiesKringen.owner == this;

 // Import candidates section...
 /** To indicate whether importing the candidates succeeded or not. */
 /*@ spec_public @*/ private static boolean importCandidatesSuccess = false;

 /** To log what went wrong during the import. */
 /*@ spec_public @*/ private static String importCandidatesError;

 /** The filename of the file read. */
 /*@ spec_public @*/ private static String importCandidatesFileName;

 /** The timestamp of the file read. */
 /*@ spec_public @*/ private static String importCandidatesFileTimestamp;

 /** The candidates reference number. */
 /*@ spec_public @*/ private static String importCandidatesRefNr;

 /** The non-negative number of kieslijsten found in the file. */
 /*@ spec_public @*/ private static int importCandidatesNrOfLists = 0;
 //@ invariant importCandidatesNrOfLists >= 0;

 /** The non-negative number of candidates found in the file. */
 /*@ spec_public @*/ private static int importCandidatesNrOfCandidates = 0;
 //@ invariant importCandidatesNrOfCandidates >= 0;

 /** The non-negative number of 'blanco' candidates. 
  *  Typically this should be one. */
 /*@ spec_public @*/ private static int importCandidatesNrOfBlanco = 0;
 //@ invariant importCandidatesNrOfBlanco >= 0;
 
 // Import votes section...

 /** To indicate whether importing the votes succeeded or not. */
 /*@ spec_public @*/ private static boolean importVotesSuccess = false;
 //@ invariant importVotesSuccess ==> importCandidatesSuccess;

 /** To log what went wrong during the import. */
 /*@ spec_public @*/ private static String importVotesError;

 /** The filename of the file read. */
 /*@ spec_public @*/ private static String importVotesFileName;

 /** The timestamp of the file read. */
 /*@ spec_public @*/ private static String importVotesFileTimestamp;

 /** The number of kieskringen found in the file with the votes. */
 /*@ spec_public @*/ private static int importVotesNrOfKieskringen = 0;
 //@ invariant importVotesNrOfKieskringen >= 0;

 /** The number of encrypted votes found in the file with the votes.
  *  Note that this includes also malformed 'votes'.
  */
 /*@ spec_public @*/ private static int importVotesNrOfVotes = 0;
 //@ invariant importVotesNrOfVotes >= decryptNrOfVotes;
 //@ invariant importVotesNrOfVotes >= countNrOfVotes;
 //@ invariant importVotesNrOfVotes >= 0;

 // Import private key section...

 /** To indicate whether importing the private key succeeded or not. */
 /*@ spec_public @*/ private static boolean importPrivKeySuccess = false;
 //@ invariant importPrivKeySuccess ==> importCandidatesSuccess;
 //@ invariant importPrivKeySuccess ==> importVotesSuccess;

 /** To log what went wrong during the import. */
 /*@ spec_public @*/ private static String importPrivKeyError;

 /** The filename of the file read. */
 /*@ spec_public @*/ private static String importPrivKeyFileName;

 /** The timestamp of the file read. */
 /*@ spec_public @*/ private static String importPrivKeyFileTimestamp;
 
 // Import public key section...

 /** To indicate whether importing the public key succeeded or not. */
 /*@ spec_public @*/ private static boolean importPubKeySuccess = false;
 //@ invariant importPubKeySuccess ==> importCandidatesSuccess;
 //@ invariant importPubKeySuccess ==> importVotesSuccess;
 //@ invariant importPubKeySuccess ==> importPrivKeySuccess;

 /** To log what went wrong during the import. */
 /*@ spec_public @*/ private static String importPubKeyError;

 /** The filename of the file read. */
 /*@ spec_public @*/ private static String importPubKeyFileName;

 /** The timestamp of the file read. */
 /*@ spec_public @*/ private static String importPubKeyFileTimestamp;

 // Keypair section...

 /** To indicate whether the private and public key match. */
 /*@ spec_public @*/ private static boolean keypairSuccess = false;
 //@ invariant keypairSuccess ==> importCandidatesSuccess;
 //@ invariant keypairSuccess ==> importVotesSuccess;
 //@ invariant keypairSuccess ==> importPrivKeySuccess;
 //@ invariant keypairSuccess ==> importPubKeySuccess;

 // Decrypt section...

 /** To indicate whether the decryption process succeeded or not. */
 /*@ spec_public @*/ private static boolean decryptSuccess = false;
 //@ invariant decryptSuccess ==> importCandidatesSuccess;
 //@ invariant decryptSuccess ==> importVotesSuccess;
 //@ invariant decryptSuccess ==> importPrivKeySuccess;
 //@ invariant decryptSuccess ==> importPubKeySuccess;
 //@ invariant decryptSuccess ==> keypairSuccess;

 /** List of the errors encountered during decryption. */
 /*@ spec_public @*/ private static String[] decryptErrors;

 /** Timestamp for start of decrypting. */
 /*@ spec_public @*/ private static String decryptTimestampStart;

 /** Timestamp for finish of decrypting. */
 /*@ spec_public @*/ private static String decryptTimestampEnd;

 /** The number of successfully decrypted votes. This includes also
  *  possible illegal votes.
  */
 /*@ spec_public @*/ private static int decryptNrOfVotes = 0;
 //@ invariant decryptNrOfVotes >= countNrOfVotes;
 //@ invariant decryptNrOfVotes >= 0;

 // Count section...

 /** To indicate whether the counting process succeeded or not. */
 /*@ spec_public @*/ private static boolean countSuccess = false;
 //@ invariant countSuccess ==> importCandidatesSuccess;
 //@ invariant countSuccess ==> importVotesSuccess;
 //@ invariant countSuccess ==> importPrivKeySuccess;
 //@ invariant countSuccess ==> importPubKeySuccess;
 //@ invariant countSuccess ==> keypairSuccess;
 //@ invariant countSuccess ==> decryptSuccess;

 /** List of the errors encountered during counting. */
 /*@ spec_public @*/ private static String[] countErrors;

 /** Timestamp for start of counting. */
 /*@ spec_public @*/ private static String countTimestampStart;

 /** Timestamp for finish of counting. */
 /*@ spec_public @*/ private static String countTimestampEnd;

 /** The number of successfully counted votes. */
 /*@ spec_public @*/ private static int countNrOfVotes = 0;
 //@ invariant countNrOfVotes >= 0;


 // Get and set methods
 /** Get the current time.
  *  @return the current time.
  */

 public /*@ pure non_null @*/ static String getCurrentTimestamp() {
   Date rightNow = new Date(System.currentTimeMillis());
   return rightNow.toString();
 }

 /** Record the timestamp for the creation of the audit log. */
 /*@ normal_behavior
   @ requires true;
   @ assignable logTimestamp;
   @ ensures logTimestamp != null;
   @*/
 public static void setLogTimestamp() {
  logTimestamp = AuditLog.getCurrentTimestamp();
 }

 /** Retrieve the timestamp for the creation of the audit log.
  *  @return creation time of the audit log.
  */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == logTimestamp;
   @*/
 /*@ pure @*/ public static String getLogTimestamp() {
  return logTimestamp;
 }

 /** Record the voting interval. 
  *  @param s the voting interval.
  */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable votingInterval;
   @ ensures votingInterval == s;
   @*/
 public static void setVotingInterval(String s) {
  votingInterval = s;
 }

 /** Retrieve the voting interval.
  *  @return the voting interval.
  */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == votingInterval;
   @*/
 /*@ pure @*/ public static String getVotingInterval() {
  return votingInterval;
 }

 /** Record the number of registered voters. 
  *  @param i the number of registered voters.
  */
 /*@ normal_behavior
   @ requires i >= 0;
   @ requires i >= countNrOfVotes;
   @ requires i >= decryptNrOfVotes;
   @ requires i >= importVotesNrOfVotes;
   @ assignable votingNrOfRegisteredVoters;
   @ assignable votingNrOfRegisteredVotersSet;
   @ ensures votingNrOfRegisteredVoters == i;
   @ ensures votingNrOfRegisteredVotersSet;
   @*/
 public static void setVotingNrOfRegisteredVoters(int i) {
  votingNrOfRegisteredVoters = i;
  votingNrOfRegisteredVotersSet = true;
 }

 /** Retrieve the number of registered voters. 
  *  @return the number of registered voters.
  */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == votingNrOfRegisteredVoters;
   @*/
 /*@ pure @*/ public static int getVotingNrOfRegisteredVoters() {
  return votingNrOfRegisteredVoters;
 }

 // Import Candidates section...

 /** Record whether importing the candidates was successful. 
  *  @param b successful or not. */
 /*@ normal_behavior
   @ assignable importCandidatesSuccess;
   @ ensures importCandidatesSuccess == b;
   @*/
 public static void setImportCandidatesSuccess(boolean b) {
  importCandidatesSuccess = b;
 } 

 /** Retrieve whether importing the candidates was successful. 
  *  @return successful or not. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == importCandidatesSuccess;
   @*/
 /*@ pure @*/ public static boolean getImportCandidatesSuccess() {
  return importCandidatesSuccess;
 } 

 /** Record errors encountered during the import of candidates. 
  *  @param s the error text. */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable importCandidatesError;
   @ ensures importCandidatesError == s;
   @*/
 public static void setImportCandidatesError(String s) {
  importCandidatesError = s;
 }

 /** Retrieve errors encountered during the import of candidates. 
  *  @return the error text. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == importCandidatesError;
   @*/
 /*@ pure @*/ public static String getImportCandidatesError() {
  return importCandidatesError;
 }

 /** Record the name of the candidate file.
  *  @param s the filename. */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable importCandidatesFileName;
   @ ensures importCandidatesFileName == s;
   @*/
 public static void setImportCandidatesFileName(String s) {
  importCandidatesFileName = s;
 }

 /** Retrieve the name of the candidate file. 
  *  @return the filename. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == importCandidatesFileName;
   @*/
 /*@ pure @*/ public static String getImportCandidatesFileName() {
  return importCandidatesFileName;
 }

 /** Record modification time of the candidate file.
  *  @param s the modification time. */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable importCandidatesFileTimestamp;
   @ ensures importCandidatesFileTimestamp == s;
   @*/
 public static void setImportCandidatesFileTimestamp(String s) {
  importCandidatesFileTimestamp = s;
 }

 /** Retrieve modification time of the candidate file. 
  *  @return the modification time. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == importCandidatesFileTimestamp;
   @*/
 /*@ pure @*/ public static String getImportCandidatesFileTimestamp() {
  return importCandidatesFileTimestamp;
 }

 /** Record the candidates reference number.
  *  @param s the candidate reference number. */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable importCandidatesRefNr;
   @ ensures importCandidatesRefNr == s;
   @*/
 public static void setImportCandidatesRefNr(String s) {
  importCandidatesRefNr = s;
 }

 /** Retrieve the candidates reference number. 
  *  @return the candidate reference number. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == importCandidatesRefNr;
   @*/
 /*@ pure @*/ public static String getImportCandidatesRefNr() {
  return importCandidatesRefNr;
 }

 /** Record the number of candidate lists (kieslijsten).
  *  @param i the number of kieslijsten.
  */
 /*@ normal_behavior
   @ requires i >= 0;
   @ assignable importCandidatesNrOfLists;
   @ ensures importCandidatesNrOfLists == i;
   @*/
 public static void setImportCandidatesNrOfLists(int i) {
  importCandidatesNrOfLists = i;
 }

 /** Retrieve the number of candidate lists (kieslijsten). 
  *  @return the number of kieslijsten.
  */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == importCandidatesNrOfLists;
   @*/
 /*@ pure @*/ public static int getImportCandidatesNrOfLists() {
  return importCandidatesNrOfLists;
 }

 /** Record the number of candidates.
  *  @param i the number of candidates.
  */
 /*@ normal_behavior
   @ requires i >= 0;
   @ assignable importCandidatesNrOfCandidates;
   @ ensures importCandidatesNrOfCandidates == i;
   @*/
 public static void setImportCandidatesNrOfCandidates(int i) {
  importCandidatesNrOfCandidates = i;
 }

 /** Retrieve the number of candidates. 
  *  @return the number of candidates.
  */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == importCandidatesNrOfCandidates;
   @*/
 /*@ pure @*/ public static int getImportCandidatesNrOfCandidates() {
  return importCandidatesNrOfCandidates;
 }

 /** Record the number of BLANCO candidates.
  *  @param i the number of BLANCO candidates. Typically, this should be 1.
  */
 /*@ normal_behavior
   @ requires i >= 0;
   @ assignable importCandidatesNrOfBlanco;
   @ ensures importCandidatesNrOfBlanco == i;
   @*/
 public static void setImportCandidatesNrOfBlanco(int i) {
  importCandidatesNrOfBlanco = i;
 }

 /** Retrieve the number of BLANCO candidates. 
  *  @return the number of BLANCO candidates. Typically, this should be 1.
  */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == importCandidatesNrOfBlanco;
   @*/
 /*@ pure @*/ public static int getImportCandidatesNrOfBlanco() {
  return importCandidatesNrOfBlanco;
 }

 // Votes section...

 /** Record whether importing the encrypted votes was successful. 
  *  @param b successful or not. */
 /*@ normal_behavior
   @ assignable importVotesSuccess;
   @ ensures importVotesSuccess == b;
   @*/
 public static void setImportVotesSuccess(boolean b) {
  importVotesSuccess = b;
 } 

 /** Retrieve whether importing the encrypted votes was successful.
  *  @return successful or not. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == importVotesSuccess;
   @*/
 /*@ pure @*/ public static boolean getImportVotesSuccess() {
  return importVotesSuccess;
 } 

 /** Record errors encountered during the import of votes.
  *  @param s the errors.
  */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable importVotesError;
   @ ensures importVotesError == s;
   @*/
 public static void setImportVotesError(String s) {
  importVotesError = s;
 }

 /** Retrieve errors encountered during the import of votes. 
  *  @return the errors. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == importVotesError;
   @*/
 /*@ pure @*/ public static String getImportVotesError() {
  return importVotesError;
 }

 /** Record the name of the vote file.
  *  @param s the filename. */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable importVotesFileName;
   @ ensures importVotesFileName == s;
   @*/
 public static void setImportVotesFileName(String s) {
  importVotesFileName = s;
 }

 /** Retrieve the name of the vote file. 
  *  @return the filename. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == importVotesFileName;
   @*/
 /*@ pure @*/ public static String getImportVotesFileName() {
  return importVotesFileName;
 }

 /** Record modification time of the vote file.
  *  @param s the modification time. */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable importVotesFileTimestamp;
   @ ensures importVotesFileTimestamp == s;
   @*/
 public static void setImportVotesFileTimestamp(String s) {
  importVotesFileTimestamp = s;
 }

 /** Retrieve modification time of the vote file. 
  *  @return the modification time. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == importVotesFileTimestamp;
   @*/
 /*@ pure @*/ public static String getImportVotesFileTimestamp() {
  return importVotesFileTimestamp;
 }

 /** Record the number of kieskringen.
  *  @param i the number of kieskringen. */
 /*@ normal_behavior
   @ requires i >= 0;
   @ assignable importVotesNrOfKieskringen;
   @ ensures importVotesNrOfKieskringen == i;
   @*/
 public static void setImportVotesNrOfKieskringen(int i) {
  importVotesNrOfKieskringen = i;
 }

 /** Retrieve the number of kieskringen. 
  *  @return the number of kieskringen. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == importVotesNrOfKieskringen;
   @*/
 /*@ pure @*/ public static int getImportVotesNrOfKieskringen() {
  return importVotesNrOfKieskringen;
 }

 /** Record the number of votes.
  *  @param i the number of votes. */
 /*@ normal_behavior
   @ requires i >= 0;
   @ requires votingNrOfRegisteredVotersSet ==> votingNrOfRegisteredVoters >= i;
   @ requires i >= countNrOfVotes;
   @ requires i >= decryptNrOfVotes;
   @ assignable importVotesNrOfVotes;
   @ ensures importVotesNrOfVotes == i;
   @*/
 public static void setImportVotesNrOfVotes(int i) {
  importVotesNrOfVotes = i;
 }

 /** Retrieve the number of votes. 
  *  @return the number of votes. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == importVotesNrOfVotes;
   @*/
 /*@ pure @*/ public static int getImportVotesNrOfVotes() {
  return importVotesNrOfVotes;
 }

 /** Record the name of the voting bureau.
  *  @param s the voting bureau. */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable votingBureau;
   @ ensures votingBureau == s;
   @*/
 public static void setVotingBureau(String s) {
  votingBureau = s;
 }

 /** Retrieve the name of the voting bureau. 
  *  @return the voting bureau. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == votingBureau;
   @*/
 /*@ pure @*/ public static String getVotingBureau() {
  return votingBureau;
 }

 /** Record the name of the voting chairman.
  *  @param s the voting chairman. */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable votingChairman;
   @ ensures votingChairman == s;
   @*/
 public static void setVotingChairman(String s) {
  votingChairman = s;
 }

 /** Retrieve the name of the voting chairman.
  *  @return the voting chairman. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == votingChairman;
   @*/
 /*@ pure @*/ public static String getVotingChairman() {
  return votingChairman;
 }

 /** Record the voting state.
  *  @param s the voting state. */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable votingState;
   @ ensures votingState == s;
   @*/
 public static void setVotingState(String s) {
  votingState = s;
 }

 /** Retrieve the voting state. 
  *  @return the voting state. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == votingState;
   @*/
 /*@ pure @*/ public static String getVotingState() {
  return votingState;
 }

 /** Record the name of the election.
  *  @param s the election. */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable votingElection;
   @ ensures votingElection == s;
   @*/
 public static void setVotingElection(String s) {
  votingElection = s;
 }

 /** Retrieve the name of the election.
  *  @return the election. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == votingElection;
   @*/
 /*@ pure @*/ public static String getVotingElection() {
  return votingElection;
 }

 /** Record the start time of the election.
  *  @param s the start time of the election. */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable votingElectionTimestampStart;
   @ ensures votingElectionTimestampStart == s;
   @*/
 public static void setVotingElectionTimestampStart(String s) {
  votingElectionTimestampStart = s;
 }

 /** Retrieve the start time of the election.
  *  @return the start time of the election. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == votingElectionTimestampStart;
   @*/
 /*@ pure @*/ public static String getVotingElectionTimestampStart() {
  return votingElectionTimestampStart;
 }

 /** Record the end time of the election.
  *  @param s the end time of the election. */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable votingElectionTimestampEnd;
   @ ensures votingElectionTimestampEnd == s;
   @*/
 public static void setVotingElectionTimestampEnd(String s) {
  votingElectionTimestampEnd = s;
 }

 /** Retrieve the end time of the election. 
  *  @return the end time of the election. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == votingElectionTimestampEnd;
   @*/
 /*@ pure @*/ public static String getVotingElectionTimestampEnd() {
  return votingElectionTimestampEnd;
 }

 /** Record the timestamp of the export of the votes.
  *  @param s the timestamp of the export of the votes. */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable votingExportTimestamp;
   @ ensures votingExportTimestamp == s;
   @*/
 public static void setVotingExportTimestamp(String s) {
  votingExportTimestamp = s;
 }

 /** Retrieve the timestamp of the export of the votes.
  *  @return the timestamp of the export of the votes. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == votingExportTimestamp;
   @*/
 /*@ pure @*/ public static String getVotingExportTimestamp() {
  return votingExportTimestamp;
 }

 // Import private key section...

 /** Record whether importing the private key was successful. 
  *  @param b successful or not. */
 /*@ normal_behavior
   @ assignable importPrivKeySuccess;
   @ ensures importPrivKeySuccess == b;
   @*/
 public static void setImportPrivKeySuccess(boolean b) {
  importPrivKeySuccess = b;
 } 

 /** Retrieve whether importing the private key was successful.
  *  @return successful or not. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == importPrivKeySuccess;
   @*/
 /*@ pure @*/ public static boolean getImportPrivKeySuccess() {
  return importPrivKeySuccess;
 } 

 /** Record errors encountered during the import of the private key.
  *  @param s the errors.
  */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable importPrivKeyError;
   @ ensures importPrivKeyError == s;
   @*/
 public static void setImportPrivKeyError(String s) {
  importPrivKeyError = s;
 }

 /** Retrieve errors encountered during the import of the private key. 
  *  @return the errors. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == importPrivKeyError;
   @*/
 /*@ pure @*/ public static String getImportPrivKeyError() {
  return importPrivKeyError;
 }

 /** Record the name of the private key file.
  *  @param s the filename. */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable importPrivKeyFileName;
   @ ensures importPrivKeyFileName == s;
   @*/
 public static void setImportPrivKeyFileName(String s) {
  importPrivKeyFileName = s;
 }

 /** Retrieve the name of the private key file. 
  *  @return the filename. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == importPrivKeyFileName;
   @*/
 /*@ pure @*/ public static String getImportPrivKeyFileName() {
  return importPrivKeyFileName;
 }

 /** Record modification time of the private key file.
  *  @param s the modification time. */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable importPrivKeyFileTimestamp;
   @ ensures importPrivKeyFileTimestamp == s;
   @*/
 public static void setImportPrivKeyFileTimestamp(String s) {
  importPrivKeyFileTimestamp = s;
 }

 /** Retrieve modification time of the private key file. 
  *  @return the modification time. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == importPrivKeyFileTimestamp;
   @*/
 /*@ pure @*/ public static String getImportPrivKeyFileTimestamp() {
  return importPrivKeyFileTimestamp;
 }

 // Import public key section...

 /** Record whether importing the public key was successful. 
  *  @param b successful or not. */
 /*@ normal_behavior
   @ assignable importPubKeySuccess;
   @ ensures importPubKeySuccess == b;
   @*/
 public static void setImportPubKeySuccess(boolean b) {
  importPubKeySuccess = b;
 } 

 /** Retrieve whether importing the public key was successful. 
  *  @return successful or not. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == importPubKeySuccess;
   @*/
 /*@ pure @*/ public static boolean getImportPubKeySuccess() {
  return importPubKeySuccess;
 } 

 /** Record errors encountered during the import of the public key.
  *  @param s the errors.
  */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable importPubKeyError;
   @ ensures importPubKeyError == s;
   @*/
 public static void setImportPubKeyError(String s) {
  importPubKeyError = s;
 }

 /** Retrieve errors encountered during the import of the public key. 
  *  @return the errors.
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == importPubKeyError;
   @*/
 /*@ pure @*/ public static String getImportPubKeyError() {
  return importPubKeyError;
 }

 /** Record the name of the public key file.
  *  @param s the filename. */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable importPubKeyFileName;
   @ ensures importPubKeyFileName == s;
   @*/
 public static void setImportPubKeyFileName(String s) {
  importPubKeyFileName = s;
 }

 /** Retrieve the name of the public key file. 
  *  @return the filename. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == importPubKeyFileName;
   @*/
 /*@ pure @*/ public static String getImportPubKeyFileName() {
  return importPubKeyFileName;
 }

 /** Record modification time of the public key file.
  *  @param s the modification time. */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable importPubKeyFileTimestamp;
   @ ensures importPubKeyFileTimestamp == s;
   @*/
 public static void setImportPubKeyFileTimestamp(String s) {
  importPubKeyFileTimestamp = s;
 }

 /** Retrieve modification time of the public key file. 
  *  @return the modification time. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == importPubKeyFileTimestamp;
   @*/
 /*@ pure @*/ public static String getImportPubKeyFileTimestamp() {
  return importPubKeyFileTimestamp;
 }

 // Keypair section...

 /** Record whether the private key and the public key form a pair. 
  *  @param b successful or not. */
 /*@ normal_behavior
   @ assignable keypairSuccess;
   @ ensures keypairSuccess == b;
   @*/
 public static void setKeypairSuccess(boolean b) {
  keypairSuccess = b;
 } 

 /** Retrieve whether the private key and the public key form a pair. 
  *  @return successful or not. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == keypairSuccess;
   @*/
 /*@ pure @*/ public static boolean getKeypairSuccess() {
  return keypairSuccess;
 } 

 // Decrypt section...

 /** Record whether the decrypt process was successful or not.
  *  @param b successful or not. */
 /*@ normal_behavior
   @ assignable decryptSuccess;
   @ ensures decryptSuccess == b;
   @*/
 public static void setDecryptSuccess(boolean b) {
  decryptSuccess = b;
 } 

 /** Retrieve whether the decrypt process was successful or not. 
  *  @return successful or not. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == decryptSuccess;
   @*/
 /*@ pure @*/ public static boolean getDecryptSuccess() {
  return decryptSuccess;
 } 

 /** Record errors encountered during decryption of the votes.
  *  @param s the errors.
  */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable decryptErrors;
   @ ensures decryptErrors == s;
   @*/
 public static void setDecryptErrors(String[] s) {
  decryptErrors = s;
 }

 /** Retrieve errors encountered during decryption of the votes. 
  *  @return the errors. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == decryptErrors;
   @*/
 /*@ pure @*/ public static String[] getDecryptErrors() {
  return decryptErrors;
 }

 /** Record the start time of the decryption.
  *  @param s the start time of the decryption. */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable decryptTimestampStart;
   @ ensures decryptTimestampStart == s;
   @*/
 public static void setDecryptTimestampStart(String s) {
  decryptTimestampStart = s;
 }

 /** Retrieve the start time of the decryption. 
  *  @return the start time of the decryption. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == decryptTimestampStart;
   @*/
 /*@ pure @*/ public static String getDecryptTimestampStart() {
  return decryptTimestampStart;
 }

 /** Record the end time of the decryption.
  *  @param s the end time of the decryption */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable decryptTimestampEnd;
   @ ensures decryptTimestampEnd == s;
   @*/
 public static void setDecryptTimestampEnd(String s) {
  decryptTimestampEnd = s;
 }

 /** Retrieve the end time of the decryption.
  *  @return the end time of the decryption */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == decryptTimestampEnd;
   @*/
 /*@ pure @*/ public static String getDecryptTimestampEnd() {
  return decryptTimestampEnd;
 }

 /** Record the number of votes decrypted. 
  *  @param i the number of votes decrypted. */
 /*@ normal_behavior
   @ requires i >= 0;
   @ requires importVotesNrOfVotes >= i;
   @ requires i >= countNrOfVotes;
   @ assignable decryptNrOfVotes;
   @ ensures decryptNrOfVotes == i;
   @*/
 public static void setDecryptNrOfVotes(int i) {
  decryptNrOfVotes = i;
 }

 /** Retrieve the number of votes decrypted. 
  *  @return the number of votes decrypted. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == decryptNrOfVotes;
   @*/
 /*@ pure @*/ public static int getDecryptNrOfVotes() {
  return decryptNrOfVotes;
 }

 // Count section...

 /** Record whether the count process was successful or not.
  *  @param b successful or not. */
 /*@ normal_behavior
   @ assignable countSuccess;
   @ ensures countSuccess == b;
   @*/
 public static void setCountSuccess(boolean b) {
  countSuccess = b;
 } 

 /** Retrieve whether the count process was successful or not. 
  *  @return successful or not. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == countSuccess;
   @*/
 /*@ pure @*/ public static boolean getCountSuccess() {
  return countSuccess;
 } 

 /** Record errors encountered during counting of the votes.
  *  @param s the errors.
  */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable countErrors;
   @ ensures countErrors == s;
   @*/
 public static void setCountErrors(String[] s) {
  countErrors = s;
 }

 /** Retrieve errors encountered during counting of the votes. 
  *  @return the errors.
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == countErrors;
   @*/
 /*@ pure @*/ public static String[] getCountErrors() {
  return countErrors;
 }

 /** Record the start time of the counting process.
  *  @param s the start time of the counting process. */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable countTimestampStart;
   @ ensures countTimestampStart == s;
   @*/
 public static void setCountTimestampStart(String s) {
  countTimestampStart = s;
 }

 /** Retrieve the start time of the counting process.
  *  @return the start time of the counting process. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == countTimestampStart;
   @*/
 /*@ pure @*/ public static String getCountTimestampStart() {
  return countTimestampStart;
 }

 /** Record the end time of the counting process.
  *  @param s the end time of the counting process. */
 /*@ normal_behavior
   @ requires s != null;
   @ assignable countTimestampEnd;
   @ ensures countTimestampEnd == s;
   @*/
 public static void setCountTimestampEnd(String s) {
  countTimestampEnd = s;
 }

 /** Retrieve the end time of the counting process.
  *  @return the end time of the counting process. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == countTimestampEnd;
   @*/
 /*@ pure @*/ public static String getCountTimestampEnd() {
  return countTimestampEnd;
 }

 /** Record the number of votes counted. 
  *  @param i the number of votes counted. */
 /*@ normal_behavior
   @ requires i >= 0;
   @ requires i <= decryptNrOfVotes;
   @ assignable countNrOfVotes;
   @ ensures countNrOfVotes == i;
   @*/
 public static void setCountNrOfVotes(int i) {
  countNrOfVotes = i;
 }

 /** Retrieve the number of votes counted. */
 /*@ normal_behavior
   @ requires true;
   @ ensures \result == countNrOfVotes;
   @*/
 /*@ pure @*/ public static int getCountNrOfVotes() {
  return countNrOfVotes;
 }


 /**
   * Returns a Source object for this object so it can be used as input for
   * a JAXP transformation.
   * @return Source The Source object
   */
 
 public /*@ pure @*/ static Source getSourceForAuditLog() {
    SAXSource saxSource = new SAXSource();
    saxSource.setXMLReader(new AuditLogXMLReader());
    return saxSource;
 }

  /*@ normal_behavior
    @   requires (* all parameters must be of the proper length *);
    @   requires 0 <= number && number <= CandidateList.MAX_KIESKRINGEN_PER_CANDIDATE_LIST;
    @   requires name.length() <= KiesKring.KIESKRING_NAME_MAX_LENGTH;
    @   modifies \everything;
    @   ensures (* all fields are properly initialized *);
    @   ensures \result.number() == number;
    @   ensures \result.name().equals(name);
    @*/
  public static /*@ non_null @*/ KiesKring addKiesKring(final byte number,
                                                        final /*@ non_null @*/ String name) {
    KiesKring kiesKring = KiesKring.make(number, name);
    kiesKringen.put(new Byte(kiesKring.number()), kiesKring);
    return kiesKring;
  }

  /*@ normal_behavior
    // @ requires new Byte(a_kieskring_number) != null;
    // ESCJava2 aborts on this line with a NoSuchElementException.
    @ ensures \result ==> kiesKringen.containsKey(new Byte(a_kieskring_number));
    @ ensures \result <== kiesKringen.containsKey(new Byte(a_kieskring_number));
    @*/
  public static /*@ pure @*/ boolean hasKiesKring(byte a_kieskring_number) {
    return kiesKringen.containsKey(new Byte(a_kieskring_number));
  }

  /**
   * Resets everything to the initial values.
   */
  /*@ normal_behavior
    @ assignable logTimestamp;
    @ assignable votingInterval;
    @ assignable votingNrOfRegisteredVoters;
    @ assignable votingBureau;
    @ assignable votingChairman;
    @ assignable votingState;
    @ assignable votingElection;
    @ assignable votingElectionTimestampStart;
    @ assignable votingElectionTimestampEnd;
    @ assignable votingExportTimestamp;
    @ assignable kiesKringen;
    @ assignable importCandidatesSuccess;
    @ assignable importCandidatesError;
    @ assignable importCandidatesFileName;
    @ assignable importCandidatesFileTimestamp;
    @ assignable importCandidatesRefNr;
    @ assignable importCandidatesNrOfLists;
    @ assignable importCandidatesNrOfCandidates;
    @ assignable importCandidatesNrOfBlanco;
    @ assignable importVotesSuccess;
    @ assignable importVotesError;
    @ assignable importVotesFileName;
    @ assignable importVotesFileTimestamp;
    @ assignable importVotesNrOfKieskringen;
    @ assignable importVotesNrOfVotes;
    @ assignable importPrivKeySuccess;
    @ assignable importPrivKeyError;
    @ assignable importPrivKeyFileName;
    @ assignable importPrivKeyFileTimestamp;
    @ assignable importPubKeySuccess;
    @ assignable importPubKeyError;
    @ assignable importPubKeyFileName;
    @ assignable importPubKeyFileTimestamp;
    @ assignable keypairSuccess;
    @ assignable decryptSuccess;
    @ assignable decryptErrors;
    @ assignable decryptTimestampStart;
    @ assignable decryptTimestampEnd;
    @ assignable decryptNrOfVotes;
    @ assignable countSuccess;
    @ assignable countErrors;
    @ assignable countTimestampStart;
    @ assignable countTimestampEnd;
    @ assignable countNrOfVotes;
    @ ensures logTimestamp.equals("");
    @ ensures votingInterval.equals("");
    @ ensures votingNrOfRegisteredVoters == 0;
    @ ensures votingBureau.equals("");
    @ ensures votingChairman.equals("");
    @ ensures votingState.equals("");
    @ ensures votingElection.equals("");
    @ ensures votingElectionTimestampStart.equals("");
    @ ensures votingElectionTimestampEnd.equals("");
    @ ensures votingExportTimestamp.equals("");
    @ ensures kiesKringen.isEmpty();
    @ ensures !importCandidatesSuccess;
    @ ensures importCandidatesError.equals("");
    @ ensures importCandidatesFileName.equals("");
    @ ensures importCandidatesFileTimestamp.equals("");
    @ ensures importCandidatesRefNr.equals("");
    @ ensures importCandidatesNrOfLists == 0;
    @ ensures importCandidatesNrOfCandidates == 0;
    @ ensures importCandidatesNrOfBlanco == 0;
    @ ensures !importVotesSuccess;
    @ ensures importVotesError.equals("");
    @ ensures importVotesFileName.equals("");
    @ ensures importVotesFileTimestamp.equals("");
    @ ensures importVotesNrOfKieskringen == 0;
    @ ensures importVotesNrOfVotes == 0;
    @ ensures !importPrivKeySuccess;
    @ ensures importPrivKeyError.equals("");
    @ ensures importPrivKeyFileName.equals("");
    @ ensures importPrivKeyFileTimestamp.equals("");
    @ ensures !importPubKeySuccess;
    @ ensures importPubKeyError.equals("");
    @ ensures importPubKeyFileName.equals("");
    @ ensures importPubKeyFileTimestamp.equals("");
    @ ensures !keypairSuccess;
    @ ensures !decryptSuccess;
    @ ensures decryptErrors == null;
    @ ensures decryptTimestampStart.equals("");
    @ ensures decryptTimestampEnd.equals("");
    @ ensures decryptNrOfVotes == 0;
    @ ensures !countSuccess;
    @ ensures countErrors == null;
    @ ensures countTimestampStart.equals("");
    @ ensures countTimestampEnd.equals("");
    @ ensures countNrOfVotes == 0;
    @*/
  public static void clear() {
    // General section...
    logTimestamp = "";
    votingInterval = "";
    votingNrOfRegisteredVoters = 0;
    votingBureau = "";
    votingChairman = "";
    votingState = "";
    votingElection = "";
    votingElectionTimestampStart = "";
    votingElectionTimestampEnd = "";
    votingExportTimestamp = "";
    kiesKringen.clear();

    // Import candidates section...
    importCandidatesSuccess = false;
    importCandidatesError = "";
    importCandidatesFileName = "";
    importCandidatesFileTimestamp = "";
    importCandidatesRefNr = "";
    importCandidatesNrOfLists = 0;
    importCandidatesNrOfCandidates = 0;
    importCandidatesNrOfBlanco = 0;
    
    // Import votes section...
    importVotesSuccess = false;
    importVotesError = "";
    importVotesFileName = "";
    importVotesFileTimestamp = "";
    importVotesNrOfKieskringen = 0;
    importVotesNrOfVotes = 0;
   
    // Import private key section...
    importPrivKeySuccess = false;
    importPrivKeyError = "";
    importPrivKeyFileName = "";
    importPrivKeyFileTimestamp = "";
 
    // Import public key section...
    importPubKeySuccess = false;
    importPubKeyError = "";
    importPubKeyFileName = "";
    importPubKeyFileTimestamp = "";

    // Keypair section...
    keypairSuccess = false;

    // Decrypt section...
    decryptSuccess = false;
    decryptErrors = null;
    decryptTimestampStart = "";
    decryptTimestampEnd = "";
    decryptNrOfVotes = 0;

    // Count section...
    countSuccess = false;
    countErrors = null;
    countTimestampStart = "";
    countTimestampEnd = "";
    countNrOfVotes = 0;

  }
}
