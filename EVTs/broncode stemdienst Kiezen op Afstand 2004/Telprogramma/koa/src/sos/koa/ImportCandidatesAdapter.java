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
 * Class to handle importing candidate file.
 *
 * @version $Id: ImportCandidatesAdapter.java,v 1.56 2004/05/28 20:37:23 hubbers Exp $
 *
 * @author Martijn Oostdijk (martijno@cs.kun.nl)
 */
public class ImportCandidatesAdapter extends Task
{
   /** The candidate list. */
   CandidateList candidates; //@ in objectState;

   /** Number of codes encountered thus far. */
   int taskCount; //@ in objectState;

   /** Whether to keep importing. Gets set to false when task is canceled. */
   boolean keepRunning; //@ in objectState;

   /**
    * Constructs this adapter.
    */
   public ImportCandidatesAdapter() {
   }

   /**
    * The title of this task.
    *
    * @return Title of this task.
    */
   String getTitle() {
      return IMPORT_CANDIDATES_TASK_MSG;
   }

   /**
    * What to print in success dialog.
    *
    * @return text to print in success dialog.
    */
   String getSuccessMessage() {
      return IMPORT_CANDIDATES_SUCCESS_MSG;
   }

   /**
    * What to print in failure dialog.
    *
    * @return text to print in failure dialog.
    */
   String getFailureMessage() {
      return IMPORT_CANDIDATES_FAILURE_MSG;
   }

   /*@ pure */ boolean isPreStateAllowed(int state) {
      return (state == CLEARED_STATE);
   }

   /**
    * The application state after successful completion of this task.
    *
    * @return the new state.
    */
   int getSuccessState() {
      return CANDIDATES_IMPORTED_STATE;
   }

   /**
    * Indicates whether the effect of this task can be undone (and whether the
    * user should be given the option to undo the task). This task is
    * cancelable, so should return <code>true</code>.
    *
    * @return this task is cancelable, so <code>true</code>.
    */
   boolean isCancelableTask() {
      return true;
   }

   /**
    * Imports the candidates.
    * Asks the user to select the file.
    * Checks the file.
    * Parses the file.
    *
    * @throws KOAException if importing failed.
    */
   /*
     @ also
     @ assignable objectState;
     @*/
   void doAction() throws KOAException {
      keepRunning = true;
      taskCount = 0;
      File file = popupGetFile(".xml", "Kandidaatbestanden (*.xml)");
      setMaxSubTasks((int)((2 * file.length())/24));
      (new CandidateFileChecker()).check(file);
      setMaxSubTasks(2 * taskCount);
      (new CandidateFileParser()).parse(file);
      MenuPanel.getTheMenuPanel().setCandidateList(candidates);
      candidates = null;
   }

   /** If the cancel button is pressed this thread should stop */
   /*@
     @ also
     @ assignable objectState;
     @ ensures !keepRunning;
     @ ensures candidates.totalPartyCount() == 0;
     @*/
   void stopAction() {
      keepRunning = false;
      clear();
   }

   /**
    * Clears temporary memory used by this task.
    */
   void clear() {
      if (candidates != null) {
         candidates.clear();
      }
      if (MenuPanel.getTheMenuPanel().getCandidateList() != null) {
         MenuPanel.getTheMenuPanel().getCandidateList().clear();
      }
   }

   /**
    * Writes a 'task started' entry in the log.
    */
   void logStarted() {
   }

   /**
    * Writes a 'task opened file' entry in the log.
    */
   void logOpenedFile(File file) {
      Date candidateFileModification = new Date(file.lastModified());
      AuditLog.setImportCandidatesFileName(file.toString());
      AuditLog.setImportCandidatesFileTimestamp(candidateFileModification.toString());
   }

   /**
    * Writes a 'task failed' entry in the log.
    */
   void logFailed(String reason) {
      AuditLog.setImportCandidatesSuccess(false);
      AuditLog.setImportCandidatesError(reason);
   }

   /**
    * Writes a 'task completed' entry in the log.
    */
   void logCompleted() {
      AuditLog.setImportCandidatesSuccess(true);
   }

   /**
    * Inner class to do light-weight sanity check on xml file.
    * If check terminates normally on a file, then it's likely to
    * be a candidate file.
    * 
    * I'd love to replace this with a DTD validity checker, but
    * the example input files do not contain doctype info.
    */
   class CandidateFileChecker extends DefaultHandler {

      int resultCount = 0; //@ in objectState;
      int metadataCount = 0; //@ in objectState;
      int kieskringCount = 0; //@ in objectState;
      int kieslijstCount = 0; //@ in objectState;
      int positieCount = 0; //@ in objectState;

      /**
       * Checks to see if <code>file</code> is likely
       * to be an XML file containing candidates. Note
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
            if (resultCount != 1) {
               throw new SAXException("Geen <result> tag gevonden!");
            }
         } catch (SAXException se) {
            throw new KOAException("Ongeldig XML formaat!");
         } catch (Exception e) {
            throw new KOAException(e);
         }
      }

      /**
       * Checks for each open tag if it's known and whether the multiplicity
       * is allowed.
       *
       * @throws SAXException if a tag occurs too often, or an
       *                      unknown tag is encountered, or the file is
       *                      not a well-formed XML file.
       */
      /*@
        @ also
        @ requires qName != null;
        @ assignable objectState;
        @*/
      public void startElement(String uri, String localName, String qName,
                               Attributes attributes)
      throws SAXException {
         if (qName.equals("result")) {
            resultCount++;
            if (resultCount > 1) {
               throw new SAXException("Illegale <result> tag!");
            }
         } else if (qName.equals("metadata")) {
            metadataCount++;
            if (metadataCount > 1) {
               throw new SAXException("Illegale <metadata> tag!");
            }
         } else if (qName.equals("requestreference")) {
         } else if (qName.equals("responsereference")) {
         } else if (qName.equals("creationtime")) {
         } else if (qName.equals("kieskringcount")) {
         } else if (qName.equals("districtcount")) {
         } else if (qName.equals("kieslijstcount")) {
         } else if (qName.equals("positiecount")) {
         } else if (qName.equals("codecount")) {
         } else if (qName.equals("kieskring")) {
            kieskringCount++;
         } else if (qName.equals("district")) {
         } else if (qName.equals("kieslijst")) {
            kieslijstCount++;
         } else if (qName.equals("positie")) {
            positieCount++;
         } else if (qName.equals("code")) {
            if (!keepRunning) {
               throw new SAXException(TASK_CANCELED_MSG);
            }
            taskCount++;
            if (taskCount % 100 == 0) {
               setSubTaskCount(taskCount);
            }
         } else {
            throw new SAXException("Onbekende tag: <" + qName + ">");
         }
      }

      public void endElement(String uri, String localName, String qName)
      throws SAXException {
      }
   }

   /**
    * Inner class to parse the candidate list file.
    */
   class CandidateFileParser extends DefaultHandler
   {
      Stack parserState; //@ in objectState;
      StringBuffer requestreference = new StringBuffer(); //@ in objectState;
      StringBuffer responsereference = new StringBuffer(); //@ in objectState;
      StringBuffer creationtime = new StringBuffer(); //@ in objectState;
      StringBuffer kieskringcount = new StringBuffer(); //@ in objectState;
      StringBuffer districtcount = new StringBuffer(); //@ in objectState;
      StringBuffer kieslijstcount = new StringBuffer(); //@ in objectState;
      StringBuffer positiecount = new StringBuffer(); //@ in objectState;
      StringBuffer codecount = new StringBuffer(); //@ in objectState;
      KiesKring kieskring; //@ in objectState;
      KiesLijst kieslijst; //@ in objectState;
      Candidate candidate; //@ in objectState;
      StringBuffer code = new StringBuffer(); //@ in objectState;

      /**
       * Parses file <code>file</code>.
       *
       * @param file the file to parse.
       *
       * @throws KOAException when file could not be parsed.
       */
      void parse(File file) throws KOAException {
         try {
            parserState = new Stack();
            SAXParserFactory factory = SAXParserFactory.newInstance();
            factory.setValidating(false);
            SAXParser parser = factory.newSAXParser();
            parser.parse(file,this);
            //@ assert parserState.empty();
         } catch (SAXException se) {
            throw new KOAException(se.getMessage());
         } catch (Exception e) {
            e.printStackTrace();
            throw new KOAException(e);
         }
      }

      /**
       * Gets called for every open element. Pushes the name
       * onto the stack. Initializes the various string buffers.
       * Adds a candidate to the candidate list for each 'positie'
       * element encountered.
       *
       * @param uri a string.
       * @param localName a string.
       * @param qName contains the qualified name of the element.
       *
       * @throws SAXException in case of a parse error.
       */
      /*@
        @ also
        @ requires qName != null;
        @ assignable objectState;
        @*/
      public void startElement(String uri, String localName, String qName,
                               Attributes attributes)
      throws SAXException {
         if (qName.equals("metadata")) {
            requestreference.setLength(0);
            responsereference.setLength(0);
            creationtime.setLength(0);
            kieskringcount.setLength(0);
            districtcount.setLength(0);
            kieslijstcount.setLength(0);
            positiecount.setLength(0);
            codecount.setLength(0);
         } else if (qName.equals("kieskring")) {
            int kieskringNumber =
               Integer.parseInt(attributes.getValue("nummer").trim());
            String kieskringName = attributes.getValue("naam");
            kieskring =
               candidates.addKiesKring((byte)kieskringNumber,kieskringName);
         } else if (qName.equals("kieslijst")) {
            byte kieslijstNumber =
               (byte)Integer.parseInt(attributes.getValue("nummer").trim());
            String partyName = attributes.getValue("groepering").trim();
            kieslijst =
               candidates.addKiesLijst(kieskring,kieslijstNumber,partyName);
         } else if (qName.equals("positie")) {
            String position = attributes.getValue("nummer");
            String lastname = attributes.getValue("achternaam");
            String initials = attributes.getValue("voorletters");
            String firstname = attributes.getValue("roepnaam");
            String gender = attributes.getValue("geslacht");
            String city = attributes.getValue("woonplaats");
            candidate = candidates.addCandidate(kieskring,kieslijst,position,
                                                lastname,initials,firstname,
                                                gender,city);
         } else if (qName.equals("district")) {
            short districtNumber =
               (short)Integer.parseInt(attributes.getValue("nummer").trim());
            String districtName = attributes.getValue("naam").trim();
            candidates.addDistrict(kieskring,districtNumber,districtName);
         } else if (qName.equals("code")) {
            if (!keepRunning) {
               throw new SAXException(TASK_CANCELED_MSG);
            }
            code.setLength(0);
         }
         parserState.push(qName);
      }

      /**
       * Gets called when processing the ('PCDATA') contents of elements.
       * Appends characters to the various string buffers, most notably
       * to <code>code</code>.
       *
       * @param ch the character buffer containing the data.
       * @param start the offset into <code>ch</code> where unprocessed data
       *    is found.
       * @param length the length of the available unprocessed data in
       *    <code>ch</code>.
       *
       * @throws SAXException in case of a parse error.
       */
      public void characters(char[] ch, int start, int length)
      throws SAXException {
         String qName = (String)parserState.peek();
         if (qName.equals("requestreference")) {
            requestreference.append(ch,start,length);
         } else if (qName.equals("responsereference")) {
            responsereference.append(ch,start,length);
         } else if (qName.equals("creationtime")) {
            creationtime.append(ch,start,length);
         } else if (qName.equals("kieskringcount")) {
            kieskringcount.append(ch,start,length);
         } else if (qName.equals("districtcount")) {
            districtcount.append(ch,start,length);
         } else if (qName.equals("kieslijstcount")) {
            kieslijstcount.append(ch,start,length);
         } else if (qName.equals("positiecount")) {
            positiecount.append(ch,start,length);
         } else if (qName.equals("codecount")) {
            codecount.append(ch,start,length);
         } else if (qName.equals("code")) {
            code.append(ch,start,length);
         }
      }

      /**
       * Gets called for every close element.
       * The closing of the 'metadata' element marks the occasion for
       * constructing the candidate list. The closing of a 'code' element
       * results in adding the (now fully processed) code to the candidate
       * list. Pops the element name from the stack.
       *
       * @param uri a string.
       * @param localName a string.
       * @param qName the qualified name of the element.
       *
       * @throws SAXException in case of a parse error.
       */
      public void endElement(String uri, String localName, String qName)
      throws SAXException {
         if (qName.equals("metadata")) {
            candidates = new CandidateList(requestreference.toString(),
                                           responsereference.toString(),
                                           creationtime.toString(),
                                           kieskringcount.toString(),
                                           districtcount.toString(),
                                           kieslijstcount.toString(),
                                           positiecount.toString(),
                                           codecount.toString());
         } else if (qName.equals("code")) {
            if (!candidates.addCandidateCode(candidate,code.toString())) {
               throw new SAXException("Ongeldige kandidaatcode!");
            }
            taskCount++;
            if (taskCount % 100 == 0) {
               setSubTaskCount(taskCount);
            }
         }
         parserState.pop();
      }
   }

   /**
    * Indicates whether this task has additional information available 
    * on the performed work.
    *
    * @return a boolean indicating whether additional information is available.
    */
   boolean isAdditionalInfoAvailable() {
      return true;
   }

   /**
    * Gets the additional information.
    *
    * @return the additional information.
    */
   Object getAdditionalInfo() {
      int height = java.lang.Math.min(AuditLog.getImportCandidatesNrOfCandidates() + ADDITIONAL_INFO_EXTRA,
      // Since CandidateList doesn't have a simple accessor for this value
      // we take it from AuditLog. It has already been filled previous to
      // this call.
                                      ADDITIONAL_INFO_MAX_HEIGHT);
      JTextArea area = new JTextArea(height,ADDITIONAL_INFO_MAX_WIDTH);

      area.setText(showCandidates());
      area.setEditable(false);
      return new JScrollPane(area);
   }

   /**
    * Gets information to put in popup dialog after successful completion of
    * this task.
    *
    * @return some information about the successfully completed task.
    */
   String getInfo() {
      CandidateList candidates =
         MenuPanel.getTheMenuPanel().getCandidateList();
      int totalPartyCount = (int)candidates.totalPartyCount(); // incl blanco
      int totalCandidates = 0;
      int lijstCandidates = 0;
      int totalBlanco = candidates.blancoCount();
      AuditLog.setImportCandidatesRefNr(
         candidates.my_metadata.requestReference()
         + File.separator
         + candidates.my_metadata.responseReference());
      Set orderedKiesKringen = candidates.my_kieskringen.keySet(); 
      assert (orderedKiesKringen != null);
      Iterator i = orderedKiesKringen.iterator();
      assert (i != null);   
      StringBuffer info = new StringBuffer();
      while (i.hasNext()) {
         Byte b = (Byte)(i.next());
         KiesKring kiesKring = (KiesKring)(candidates.my_kieskringen.get(b));
         info.append("Kieskring ");
         info.append(kiesKring.number());
         info.append(" ");
         info.append(kiesKring.name());
         info.append("\n");
         info.append("Aantal lijsten (excl. blanco): ");
         info.append(kiesKring.kieslijstCount()-totalBlanco);
         info.append("\n\n");
         for (int j = 0; j < kiesKring.my_kiesLijsten.length; j++) {
            if (kiesKring.my_kiesLijsten[j] != null) {
	       lijstCandidates = kiesKring.my_kiesLijsten[j].candidateCount();
               totalCandidates += lijstCandidates;
               info.append("Lijst ");
               info.append(kiesKring.my_kiesLijsten[j].number());
               info.append(" ");
               info.append(kiesKring.my_kiesLijsten[j].name());
               info.append(": ");
               info.append(lijstCandidates);
               info.append("\n");
            }
         }
      }
      info.append("\nTotaal aantal kandidaten (excl. blanco): ");
      info.append(totalCandidates - totalBlanco);
      info.append("\n");
      AuditLog.setImportCandidatesNrOfLists(totalPartyCount-totalBlanco);
      AuditLog.setImportCandidatesNrOfCandidates(totalCandidates-totalBlanco);
      AuditLog.setImportCandidatesNrOfBlanco(totalBlanco);
      return info.toString();
   }

   /**
    * Gets the list of candidates imported by this task.
    *
    * @return the list of candidates imported by this task.
    */
   /*@ pure @*/ String showCandidates() {
      CandidateList candidates =
         MenuPanel.getTheMenuPanel().getCandidateList();
      StringBuffer allCandidates = new StringBuffer();
      Set orderedKiesKringen = candidates.my_kieskringen.keySet(); 
      assert (orderedKiesKringen != null);
      Iterator i = orderedKiesKringen.iterator();
      assert (i != null);   
      while (i.hasNext()) {
         Byte b = (Byte)(i.next());
         KiesKring kiesKring = (KiesKring)(candidates.my_kieskringen.get(b));
         allCandidates.append("Kieskring ");
         allCandidates.append(kiesKring.number());
         allCandidates.append(" ");
         allCandidates.append(kiesKring.name());
         allCandidates.append("\n");
         allCandidates.append("Aantal lijsten (excl. blanco): ");
         allCandidates.append((kiesKring.kieslijstCount() - candidates.blancoCount()));
         allCandidates.append("\n\n");
         for (int j = 0; j < kiesKring.getKiesLijsten().length; j++) {
            KiesLijst kiesLijst = kiesKring.getKiesLijsten()[j];     
            if (kiesLijst != null) {
               allCandidates.append("\nLijst ");
               allCandidates.append(kiesLijst.number());
               allCandidates.append(" ");
               allCandidates.append(kiesLijst.name());
               allCandidates.append(": ");
               allCandidates.append(kiesLijst.candidateCount());
               allCandidates.append("\n");
               for (int k = 0; k < kiesLijst.candidates().length; k++) {
                  Candidate candidate = kiesLijst.candidates()[k];
                  if (candidate != null) {
                     allCandidates.append(candidate.position_number());
                     allCandidates.append(" ");
                     allCandidates.append(candidate.initials());
                     allCandidates.append(" ");
                     allCandidates.append(candidate.lastname());
                     allCandidates.append("\n");
                  }
               }
            }
         }
      }
      return allCandidates.toString();
   }

   /**
    * Importing candidate codes can take a long time, better pop up a
    * progress monitor.
    *
    * @return true.
    */
   boolean isProgressMonitoredTask() {
      return true;
   }

}

