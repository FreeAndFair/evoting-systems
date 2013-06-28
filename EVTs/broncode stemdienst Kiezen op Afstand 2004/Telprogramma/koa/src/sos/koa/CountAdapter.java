/*
 * JML specification Copyright 2004 SoS Group, University of Nijmegen
 */

package sos.koa;

import java.awt.*;
import java.awt.event.*;
import java.util.*;
import javax.swing.*;

/**
 * Class to count the votes.
 *
 * @version $Id: CountAdapter.java,v 1.31 2004/05/28 20:37:23 hubbers Exp $
 * 
 * @author Martijn Oostdijk (martijno@cs.kun.nl)
 */
public class CountAdapter extends Task
{
   /** The datastructure containing counted votes. */
   /*@ spec_public @*/ VoteSet voteSet; //@ in objectState;

   /** The number of votes counted this far. */
   /*@ spec_public @*/ int votesCounted; //@ in objectState;

   /** Whether to keep counting. */
   /*@ spec_public @*/ boolean keepRunning; //@ in objectState;

   /** A list containing errors encountered this far. */
   /*@ spec_public @*/ ArrayList errors; //@ in objectState;

   /**
    * Constructs this adapter.
    */
   public CountAdapter() {
   }

   /*@ pure @*/ String getTitle() {
      return COUNT_TASK_MSG;
   }

   /*@ pure @*/ String getSuccessMessage() {
      if (errors != null && errors.size() > 0) {
         return COUNT_SUCCESS_MSG + "\n\n"
                + AuditLog.getImportVotesNrOfVotes() 
                + " stem"
                + (AuditLog.getImportVotesNrOfVotes() != 1 ? "men" : "")
                + " geïmporteerd.\n" 
                + AuditLog.getDecryptNrOfVotes() 
                + " stem"
                + (AuditLog.getDecryptNrOfVotes() != 1 ? "men" : "")
                + " ontsleuteld.\n" 
                + errors.size() 
                + " stem" 
                + (errors.size() != 1 ? "men" : "") 
                + VOTES_IGNORED_SEE_MORE_INFO_MSG;
      } else {
         return COUNT_SUCCESS_MSG + "\n\n"
                + NO_ERRORS_MSG;
      }
   }

   /*@ pure @*/ String getFailureMessage() {
      return COUNT_FAILURE_MSG;
   }

   /*@ pure @*/ boolean isPreStateAllowed(int state) {
      return (state == VOTES_DECRYPTED_STATE);
   }

   /*@ pure @*/ int getSuccessState() {
      return VOTES_COUNTED_STATE;
   }

   /*@ 
     @ also
     @ assignable AuditLog.*;
     @*/
   void logStarted() {
      AuditLog.setCountTimestampStart(AuditLog.getCurrentTimestamp());
   }

   /*@ 
     @ also
     @ assignable AuditLog.*;
     @*/
   void logCompleted() {
      AuditLog.setCountSuccess(true);
      AuditLog.setCountNrOfVotes(votesCounted);
      AuditLog.setCountTimestampEnd(AuditLog.getCurrentTimestamp());
      AuditLog.setCountErrors(getErrors());
   }

   /*@ 
     @ also
     @ assignable AuditLog.*;
     @*/
   void logFailed(String reason) {
      AuditLog.setCountSuccess(false);
      String[] err = { reason };
      AuditLog.setCountErrors(err);
   }

   /*@ pure @*/ boolean isProgressMonitoredTask() {
      return true;
   }

   /**
    * Counts the votes.
    *
    * Part indexes:
    *    0 kandidaatcode
    *    1 achternaam
    *    2 voorletters
    *    3 positienummer
    *    4 districtnummer
    *    5 kieslijstnummer
    *    6 lijstnaam
    *    7 kieskringnummer.
    */
   /*@
     @ also
     @ assignable objectState;
     @*/
   public void doAction() throws KOAException {
      errors = new ArrayList();
      votesCounted = 0;
      voteSet = new VoteSet(MenuPanel.getTheMenuPanel().getCandidateList());
      voteSet.initializeVote();
      // This should be done in stopAction, however because of
      // racing conditions we do it here. The idea is that each run
      // of doAction starts with 0 votes for each candidate.
      voteSet.resetVotes();
      ArrayList rawVotes = MenuPanel.getTheMenuPanel().getRawVotes();
      setMaxSubTasks(rawVotes.size());
      keepRunning = true;
      for (int i = 0; i < rawVotes.size(); i++) {
         if (!keepRunning) {
            throw new KOAException(TASK_CANCELED_MSG);
         }
         try {
            String vote = (String)(rawVotes.get(i));
            // Test whether decryption already failed
            
            if (vote.startsWith(DECRYPT_ERROR_TAG)) {
               // Apparently this is not a correct decrypted vote
               // Since the error message was already shown before,
               // we simply skip this vote
            } else {
               String[] parts = vote.split(";");
           
            
               // We should have candidatecode plus redundant fields
               if (parts.length < NUMBER_OF_REDUNDANT_FIELDS + 1) {
                  // Do nothing with this illegal vote
                  throw new KOAException("Rij index " + i +
                                ": Niet alle redundante informatie gevonden!");
   
               } else {
                  //@ assert parts.length >= NUMBER_OF_REDUNDANT_FIELDS + 1;
                  /* Replace string "null" with null pointer... */
                  for (int j = 0; j < parts.length; j++) {
                     if (parts[j].equals("null")) {
                        parts[j] = null;
                     }
                  }
      
                  /* Check validity of the vote. */
                  /* Is there a candidate with this code? */
                  if (!voteSet.validCandidate(parts[0])) {
                     throw new KOAException("Rij index " + i
                                       + ": Geen kandidaat gevonden met code " + parts[0]
                                       + "!");
                  }
                  /* Does the redundant info match? */
                  if (voteSet.validateRedundantInfo(parts[0],parts[1],
                                                    parts[2],parts[6],
                                                    parts[5],parts[3])) {
                     /* Does it has a valid kieskring number? */
                     if (voteSet.validateKiesKringNumber(parts[0],parts[7])) {
                        /* Count the vote. */
                        voteSet.addVote(parts[0]);
                        votesCounted++;
                     } else {
                        throw new KOAException("Rij index " + i
                                            + ": Kandidaat " + parts[0]
                                            + "; Ongeldig kieskringnummer!");
                     }
                  } else {
                     throw new KOAException("Rij index " + i
                                       + ": Kandidaat " + parts[0]
                                       + "; Ongeldige redundante informatie!");
                  }
               }
            }
         } catch (KOAException e) {
            // Apparently something went wrong counting this vote.
            // We just don't count this one.
            errors.add(e.getMessage());
         } catch (Exception e) {
            // Apparently something went wrong counting this vote.
            // We just don't count this one.
            errors.add(("Rij index " + i + ": Onbekende fout tijdens tellen."));
            // The extra '(...)' are used to avoid a jmlc bug.
         }

         if (i % 10 == 0) {
            setSubTaskCount(i);
         }
      }

      /*
       * Skip this test: it prevents creating the audit log
       *
       * if (votesCounted == 0) {
       *    throw new KOAException("Geen enkele geldige stem gevonden!");
       * }
       */
      voteSet.finalizeVote();
      MenuPanel.getTheMenuPanel().setVoteSet(voteSet);
      voteSet = null;
   }

   /*@ 
     @ also
     @ behavior
     @ assignable keepRunning;
     @ ensures !keepRunning;
     @*/
   void stopAction() {
      keepRunning = false;
      // Moved to the beginning of doAction because of race conditions.
      // This is good enough for making sure that no votes are counted
      // twice by pressing the cancel button on the progress bar.
      // voteSet.resetVotes();
   }

   /*@ pure @*/ String getInfo() {
      return Integer.toString(votesCounted)
             + " stem" + (votesCounted != 1 ? "men":"")
             + " geteld.";
   }

   /*@ pure @*/ Object getAdditionalInfo() {
      int height = java.lang.Math.min(errors.size() + ADDITIONAL_INFO_EXTRA,
                                      ADDITIONAL_INFO_MAX_HEIGHT);
      JTextArea area = new JTextArea(height,ADDITIONAL_INFO_MAX_WIDTH);
      StringBuffer additionalInfo = new StringBuffer();
      if (errors.size() > 0) {
         additionalInfo.append("De volgende fouten zijn geconstateerd:\n");
         for (int i = 0; i < errors.size(); i++) {
            additionalInfo.append(errors.get(i).toString());
            additionalInfo.append("\n");
         }
      } else {
         additionalInfo.append("Er zijn geen fouten opgetreden bij het tellen.");
      }
      area.setText(additionalInfo.toString());
      area.setEditable(false);
      return new JScrollPane(area);
   }

   /*@ pure @*/ boolean isAdditionalInfoAvailable() {
      return true;
   }

   /**
    * Gets the errors encountered during execution of this task.
    *
    * @return an array of error strings.
    */
   /*@ pure @*/ String[] getErrors() {
      String[] result = new String[errors.size()];
      errors.toArray(result);
      return result;
   }
}

