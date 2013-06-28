/*
 * JML specification Copyright 2004 SoS Group, University of Nijmegen
 */

package sos.koa;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import java.util.*;
import javax.swing.*;
import javax.xml.parsers.*;
import org.w3c.dom.*;
import org.xml.sax.*;
import org.xml.sax.helpers.*;

/**
 * Class to handle importing the votes file.
 *
 * @version $Id: ImportVotesAdapter.java,v 1.47 2004/05/28 20:37:23 hubbers Exp $
 *
 * @author Martijn Oostdijk (martijno@cs.kun.nl)
 */
public class ImportVotesAdapter extends Task
{
   /** The imported, not yet decrypted, votes. */
   /*@ spec_public */ ArrayList rawVotes; //@ in objectState;

   /** Number of rows encountered thus far. */
   int taskCount; //@ in objectState;

   /** Number of kieskringen encountered thus far. */
   int kieskringCount; //@ in objectState;

   /** Whether to keep importing. Gets set to false when task is canceled. */
   boolean keepRunning; //@ in objectState;

   /*@ public behavior
     @    assignable rawVotes;
     @    ensures rawVotes == null;
    */
   /**
    * Constructs this adapter.
    */
   public ImportVotesAdapter() {
      rawVotes = null;
   }

   /**
    * The title of this task.
    *
    * @return Title of this task.
    */
   /*@ pure non_null */ String getTitle() {
      return IMPORT_VOTES_TASK_MSG;
   }

   /*@ pure non_null */ String getSuccessMessage() {
      return IMPORT_VOTES_SUCCESS_MSG;
   }

   /*@ pure non_null */ String getFailureMessage() {
      return IMPORT_VOTES_FAILURE_MSG;
   }

   /*@ pure */ boolean isPreStateAllowed(int state) {
      return (state == CANDIDATES_IMPORTED_STATE);
   }

   /*@ pure */ int getSuccessState() {
      return VOTES_IMPORTED_STATE;
   }

   /**
    * Indicates whether the effect of this task can be undone
    * (and whether the user should be given the option to undo the task).
    *
    * @return vote importing can be undone, so <code>true</code>.
    */
   /*@ pure */ boolean isCancelableTask() {
      return true;
   }

   /*@ also
     @ behavior
     @    assignable \everything;
     @    ensures MenuPanel.getTheMenuPanel().rawVotes != null;
     @    ensures rawVotes == null;
     @    signals(KOAException) true;
    */
   /**
    * Imports the votes.
    * Asks the user for a file.
    * Checks the file.
    * Reads the file.
    *
    * @throws KOAException if importing failed.
    */
   void doAction() throws KOAException {
      kieskringCount = 0;
      taskCount = 0;
      keepRunning = true;
      rawVotes = new ArrayList();
      File file = popupGetFile(".xml", "Stembusbestanden (*.xml)");
      setMaxSubTasks((int)((2 * file.length())/268));
      (new VoteFileChecker()).check(file);
      setMaxSubTasks(2 * taskCount);
      (new VoteFileParser()).parse(file);
      MenuPanel.getTheMenuPanel().setRawVotes(rawVotes);
      rawVotes = null;
   }

   /** If the cancel button is pressed this thread should stop */
   /*@
     @ also
     @ assignable objectState;
     @ ensures !keepRunning;
     @ ensures rawVotes == null;
     @*/
   void stopAction() {
      keepRunning = false;
      clear();
   }

   /*@ also
     @ behavior
     @    ensures \result != null;
    */
   /*@ pure @*/ String getInfo() {
      int voteCount = MenuPanel.getTheMenuPanel().getRawVotes().size();
      return Integer.toString(kieskringCount)
             + " kieskring" + (kieskringCount != 1 ? "en" : "")
             + " geïmporteerd!\n"
             + Integer.toString(voteCount)
             + " stem" + (voteCount != 1 ? "men" : "")
             + " geïmporteerd!\n";
   }

   /**
    * Importing votes can take a long time, better pop up a
    * progress monitor.
    *
    * @return true.
    */
   /*@ pure */ boolean isProgressMonitoredTask() {
      return true;
   }

   void clear() {
      rawVotes = null;
      if (MenuPanel.getTheMenuPanel().getRawVotes() != null) {
         MenuPanel.getTheMenuPanel().setRawVotes(null);
      }
   }

   void logStarted() {
   }

   void logOpenedFile(File file) {
      Date votesFileModification = new Date(file.lastModified());
      AuditLog.setImportVotesFileName(file.toString());
      AuditLog.setImportVotesFileTimestamp(votesFileModification.toString());
   }

   void logCompleted() {
      int voteCount = MenuPanel.getTheMenuPanel().getRawVotes().size();
      AuditLog.setImportVotesSuccess(true);
      AuditLog.setImportVotesNrOfVotes(voteCount);
      AuditLog.setImportVotesNrOfKieskringen(kieskringCount);
   }

   void logFailed(String reason) {
      AuditLog.setImportVotesSuccess(false);
      AuditLog.setImportVotesError(reason);
   }

   /**
    * Inner class to do light-weight sanity check on xml file.
    * If check terminates normally on a file, then it's likely to
    * be a vote file.
    *
    * I'd love to replace this with a DTD validity checker, but
    * the example input files do not contain doctype info.
    */
   class VoteFileChecker extends DefaultHandler {

      int reportCount = 0;
      int globaalCount = 0;
      int kieskringenCount = 0;
      int kieskringCount = 0;
      int tableCount = 0;

      /*@ behavior
        @    requires file != null;
        @    assignable this.*;
        @    signals(KOAException) true;
       */
      /**
       * Checks to see if <code>file</code> is likely
       * to be an XML file containing exported votes. Note
       * that this does not do DTD validity checking!
       *
       * @param file the file.
       */
      void check(File file) throws KOAException {
         try {
            SAXParserFactory factory = SAXParserFactory.newInstance();
            factory.setValidating(false);
            SAXParser parser = factory.newSAXParser();
            parser.parse(file,this);
            if (tableCount < 1) {
               throw new SAXException("Geen <TABLE> tag gevonden!");
            }
         } catch (SAXException se) {
            throw new KOAException("Ongeldig XML formaat!");
         } catch (Exception e) {
            throw new KOAException(e);
         }
      }

      /*@ also
        @ public behavior
        @    requires qName != null;
        @    assignable \everything;
       */
      /**
       * Checks for each open tag if it's known and whether the multiplicity
       * is allowed.
       *
       * @throws SAXException if a tag occurs too often, or an
       *                      unknown tag is encountered, or the file is
       *                      not a well-formed XML file.
       */
      public void startElement(String uri, String localName, String qName,
                               Attributes attributes)
      throws SAXException {
         if (qName.equals("REPORT")) {
            reportCount++;
            if (reportCount != 1) {
               throw new SAXException("Illegale <REPORT> tag!");
            }
         } else if (qName.equals("GLOBAAL")) {
            globaalCount++;
            if (globaalCount != 1) {
               throw new SAXException("Illegale <GLOBAAL> tag!");
            }
         } else if (qName.equals("KIESKRINGEN")) {
            kieskringenCount++;
            if (kieskringenCount != 1) {
               throw new SAXException("Illegale <KIESKRINGEN> tag!");
            }
         } else if (qName.equals("KIESKRING")) {
            kieskringCount++;
            if (kieskringCount != 1) {
               throw new SAXException("Illegale <KIESKRING> tag!");
            }
         } else if (qName.equals("TABLE")) {
            tableCount++;
            if (tableCount != 1) {
               throw new SAXException("Illegale <TABLE> tag!");
            }
         } else if (qName.equals("ROW")) {
            taskCount++;
            if (taskCount % 100 == 0) {
               setSubTaskCount(taskCount);
            }
         } else {
            throw new SAXException("Onbekende tag: <" + qName + ">");
         }
      }
   }

   /**
    * Inner class to parse the vote file.
    */
   class VoteFileParser extends DefaultHandler
   {
      /*@ private behavior
        @    requires file != null;
        @    assignable \everything;
        @    signals(KOAException) true;
       */
      private void parse(File file) throws KOAException {
         try {
            SAXParserFactory factory = SAXParserFactory.newInstance();
            factory.setValidating(false);
            SAXParser parser = factory.newSAXParser();
            parser.parse(file,this);
         } catch (SAXException se) {
            throw new KOAException(se.getMessage());
         } catch (Exception e) {
            throw new KOAException(e);
         }
      }

      /*@ also
        @ public behavior
        @    requires qName != null;
        @    requires attributes != null;
        @    assignable \everything;
        @    signals(SAXException) true;
       */
      public void startElement(String uri, String localName, String qName,
                               Attributes attributes)
      throws SAXException {
         if (qName.equals("GLOBAAL")) {
            AuditLog.setVotingBureau(attributes.getValue("STEMBUREAU"));
            AuditLog.setVotingChairman(attributes.getValue("VOORZITTER"));
            AuditLog.setVotingState(attributes.getValue("STATE"));
            AuditLog.setVotingElection(attributes.getValue("VERKIEZING"));
            AuditLog.setVotingElectionTimestampStart(attributes.getValue("PERIODE_START"));
            AuditLog.setVotingElectionTimestampEnd(attributes.getValue("PERIODE_EIND"));
            AuditLog.setVotingExportTimestamp(attributes.getValue("CURTIME"));
         } else if (qName.equals("KIESKRING")) {
            int kieskringNumber = Integer.parseInt(attributes.getValue("NUMMER").trim());
            String kieskringName = attributes.getValue("NAAM");
            AuditLog.addKiesKring((byte)kieskringNumber,kieskringName);
            kieskringCount++;
         } else if (qName.equals("ROW")) {
            if (!keepRunning) {
               throw new SAXException(TASK_CANCELED_MSG);
            }
            String voteNumber = attributes.getValue("STEMNUMMER");
            String vote = attributes.getValue("STEM");
            byte[] hexVote = Hex.hexStringToBytes(vote);
            rawVotes.add(hexVote);
            taskCount++;
            if (taskCount % 100 == 0) {
               setSubTaskCount(taskCount);
            }
         } 
      }
   }
}

