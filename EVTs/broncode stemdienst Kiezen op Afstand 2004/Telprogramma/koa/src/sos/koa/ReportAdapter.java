/*
 * JML specification Copyright 2004 SoS Group, University of Nijmegen
 */

package sos.koa;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import java.io.File;
import java.net.*;
import java.util.*;
import javax.swing.*;
import org.xml.sax.*;

//JAXP
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.TransformerException;
import javax.xml.transform.Source;
import javax.xml.transform.Result;
import javax.xml.transform.stream.StreamSource;
import javax.xml.transform.stream.StreamResult;
import javax.xml.transform.sax.SAXSource;
import javax.xml.transform.sax.SAXResult;

//Avalon
import org.apache.avalon.framework.ExceptionUtil;
import org.apache.avalon.framework.logger.ConsoleLogger;
import org.apache.avalon.framework.logger.Logger;

//FOP
import org.apache.fop.apps.Driver;
import org.apache.fop.apps.FOPException;
import org.apache.fop.messaging.MessageHandler;

/**
 * Class to generate reports.
 *
 * @version $Id: ReportAdapter.java,v 1.27 2004/05/28 20:37:23 hubbers Exp $
 *
 * @author Engelbert Hubbers (hubbers@cs.kun.nl)
 */
public class ReportAdapter extends Task {

   String info; //@ in objectState;

   /*@ non_null @*/ String votingInterval; //@ in objectState;

   int registeredVoters; //@ in objectState;

   public ReportAdapter() {
      votingInterval = DEFAULT_VOTING_INTERVAL;
      registeredVoters = -1;
   }

   /*@ pure @*/ String getTitle() {
      return REPORT_TASK_MSG;
   }

   /*@ pure */ String getSuccessMessage() {
      return REPORT_SUCCESS_MSG;
   }

   /*@ pure @*/ String getFailureMessage() {
      return REPORT_FAILURE_MSG;
   }

   /*@ pure */ boolean isPreStateAllowed(int state) {
      return (state == VOTES_COUNTED_STATE || state == REPORT_GENERATED_STATE);
   }

   /*@ pure */ int getSuccessState() {
      return REPORT_GENERATED_STATE;
   }

   /*@ 
     @ also
     @ assignable objectState;
     @*/
   void doAction() throws KOAException {
      if (registeredVoters < 0) {
         registeredVoters = AuditLog.getImportVotesNrOfVotes();
      }
      info = "";
      int j,k;
      AuditLog.setLogTimestamp();

      int selectedValue =
         JOptionPane.showOptionDialog(MenuPanel.getTheMenuPanel(),
                                      "Kies het rapporttype",
                                      REPORT_TASK_MSG,
                                      JOptionPane.DEFAULT_OPTION,
                                      JOptionPane.QUESTION_MESSAGE,
                                      null,
                                      REPORT_OPTIONS,
                                      REPORT_OPTIONS[0]);
      switch (selectedValue) {
      case RECOUNT:
         try {
            /* Ask user for voting interval */
            votingInterval =
               JOptionPane.showInputDialog(MenuPanel.getTheMenuPanel(),
                  "Geef de stemperiode",votingInterval);
            if (votingInterval == null) {
               throw new KOAException("Ongeldige stemperiode!");
            }
            AuditLog.setVotingInterval(votingInterval);

            /* Ask user for number of registered voters*/

            registeredVoters =
               Integer.parseInt(JOptionPane.showInputDialog(MenuPanel.getTheMenuPanel(),
                  "Geef het aantal kiesgerechtigden",
                  Integer.toString(registeredVoters)));
            if (registeredVoters < 0) {
               throw new KOAException("Aantal kiesgerechtigden negatief!");
            }
            if (registeredVoters < AuditLog.getImportVotesNrOfVotes()) {
               throw new KOAException("Aantal kiesgerechtigden kleiner dan aantal stemmen!");
            }
            AuditLog.setVotingNrOfRegisteredVoters(registeredVoters);
         } catch (KOAException ke) {
           votingInterval = DEFAULT_VOTING_INTERVAL;
           registeredVoters = AuditLog.getImportVotesNrOfVotes();
           throw new KOAException(ke.getMessage());
         } catch (NumberFormatException nfe) {
           throw new KOAException("Ongeldige invoer!");
         }

         CandidateList candidates =
            MenuPanel.getTheMenuPanel().getCandidateList();

         try {
            //Setup directories
            File baseDir = new File(BASEDIR);
            File outDir = new File(baseDir, OUTDIR);
            outDir.mkdirs();
      
            //Setup input and output
            String recountXSL = getInputResource(RECOUNT_XSL);
            File xmlfile = new File(outDir, RECOUNT_XML);
            File pdffile = new File(outDir, RECOUNT_PDF);

            // Transform
            convertCandidateList2PDF(recountXSL,xmlfile,pdffile);
            info += "Bekijk de file:\n\"" + pdffile.toString() + "\"";
            ViewPdf.showPdf(pdffile);

         } catch (IOException e) {
            throw new KOAException("Probleem met IO");
         } catch (FOPException e) {
            throw new KOAException("Probleem met FOP");
         } catch (TransformerException e) {
            throw new KOAException("Probleem met de transformatie");
         } catch (Exception e) {
            throw new KOAException("Onbekende fout");
         }
         break;
      case AUDITLOG:
         try {
            //Setup directories
            File baseDir = new File(BASEDIR);
            File outDir = new File(baseDir, OUTDIR);
            outDir.mkdirs();
      
            //Setup input and output
            String auditlogXSL = getInputResource(AUDITLOG_XSL);
            File xmlfile = new File(outDir, AUDITLOG_XML);
            File pdffile = new File(outDir, AUDITLOG_PDF);

            // Transform
            convertAuditLog2PDF(auditlogXSL,xmlfile,pdffile);
            info += "Bekijk de file:\n\"" + pdffile.toString() +"\"";
            ViewPdf.showPdf(pdffile);

         } catch (IOException e) {
            throw new KOAException("Probleem met IO");
         } catch (FOPException e) {
            throw new KOAException("Probleem met FOP");
         } catch (TransformerException e) {
            throw new KOAException("Probleem met de transformatie");
         } catch (Exception e) {
            throw new KOAException("Onbekende fout");
         }
         break;
      default:
         throw new KOAException("Taak geannuleerd!");
      }

   }

   /*@ pure @*/ void logStarted() {
      // log handling is done in doAction...
   }

   /*@ pure @*/ void logCanceled() {
      // log handling is done in doAction...
   }

   /*@ pure @*/ void logOpenedFile(File file) {
      // log handling is done in doAction...
   }

   /*@ pure @*/ void logFailed(String reason) {
      // log handling is done in doAction...
   }

   /*@ pure @*/ void logCompleted() {
      // log handling is done in doAction...
   }

   /*@ pure @*/ String getInfo() {
      return info;
   }

   /*@ pure @*/ public void convertAuditLog2PDF(String xslt, File xmlOut, File pdfOut)
   throws IOException, FOPException, TransformerException {
      convertXML2PDF(new SAXSource(new AuditLogXMLReader(),
                                   new InputSource()),
                     new StreamSource(xslt),
                     new StreamResult(xmlOut),
                     new FileOutputStream(pdfOut));
   }

   /*@ pure @*/ public void convertCandidateList2PDF(String xslt, File xmlOut, File pdfOut)
   throws IOException, FOPException, TransformerException {
      CandidateList candidates =
         MenuPanel.getTheMenuPanel().getCandidateList();
      convertXML2PDF(new SAXSource(new CandidateListXMLReader(),
                                       new InputSource()),
                     new StreamSource(xslt),
                     new StreamResult(xmlOut),
                     new FileOutputStream(pdfOut));
   }

   /*@ pure @*/ private void convertXML2PDF(Source src, StreamSource xslt,
                              StreamResult xmlOut, OutputStream pdfOut)
   throws IOException, FOPException, TransformerException {

      //Construct driver
      Driver driver = new Driver();

      //Setup logger
      Logger logger = new ConsoleLogger(ConsoleLogger.LEVEL_DISABLED);
      driver.setLogger(logger);
      MessageHandler.setScreenLogger(logger);

      //Setup Renderer (output format)
      driver.setRenderer(Driver.RENDER_PDF);

      try {
         driver.setOutputStream(pdfOut);

         // Transformers - r0b0t5 in disguise... lalala...
         TransformerFactory factory = TransformerFactory.newInstance();
         Transformer transformer = factory.newTransformer(xslt);
         Transformer transformer1 = factory.newTransformer();

         //Start XSLT transformation
         transformer1.transform(src,xmlOut);

         //Resulting SAX events (the generated FO) must be piped through to FOP
         Result res = new SAXResult(driver.getContentHandler());

         //Start XSLT transformation and FOP processing
         transformer.transform(src,res);

      } finally {
         pdfOut.close();
      }
   }

   /**
    * Gets a URI string for the relative path <code>relPath</code>.
    * I've tried to make this as robust as possible. Behavior seems
    * to depend on whether the application is run from a jar or not
    * and on the operating system. -- MO
    *
    * @param relPath a relative URI path, which uses '/' as separator.
    *
    * @return a URI string for the relative path <code>relPath</code>.
    */
   /*@ pure @*/ String getInputResource(String relPath) {
      Class c = this.getClass();
      ClassLoader classLoader = null;
      URL absPath = null;

      /* Try to get a class loader. */
      if (c != null) {
         /* We prefer this class's class loader. */
         classLoader = c.getClassLoader();
      }
      if (classLoader == null) {
         /* Try to get the system classloader instead. */
         classLoader = ClassLoader.getSystemClassLoader();
      }

      if (classLoader != null) {
         /* Try to interpret relPath w.r.t. the base for class loading. */
         absPath = classLoader.getSystemResource(relPath);
      }
      if (absPath == null) {
         /* Use the fact that this class is in 'sos/koa'... ugly! */
         absPath = c.getResource("../../"+relPath);
      }

      /* If we found an URI, return it. */
      if (absPath != null) {
         return absPath.toString();
      }

      /* If all else failed, just return the relative path. */
      return relPath;
   }
}

