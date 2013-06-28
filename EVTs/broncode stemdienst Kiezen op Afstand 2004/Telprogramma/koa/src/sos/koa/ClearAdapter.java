/*
 * JML specification Copyright 2004 SoS Group, University of Nijmegen
 */

package sos.koa;

import java.io.*;
import java.awt.*;
import java.awt.event.*;
import javax.swing.*;

/**
 * Class to clear memory and files.
 *
 * @version $Id: ClearAdapter.java,v 1.21 2004/05/14 18:02:31 martijno Exp $
 *
 * @author Martijn Oostdijk (martijno@cs.kun.nl)
 */
class ClearAdapter extends Task
{
  /** A flag indicating if the system has been cleared. */
  boolean systemIsCleared;

  /**
   * Constructs a new ClearAdaptor.
   */
  /*@ normal_behavior
    @   ensures !systemIsCleared;
    @*/
  /*@ pure @*/ ClearAdapter() {
    systemIsCleared = false;
  }

   String getTitle() {
      return CLEAR_TASK_MSG;
   }

   String getSuccessMessage() {
      return CLEAR_SUCCESS_MSG;
   }

   String getFailureMessage() {
      return CLEAR_FAILURE_MSG;
   }

   String getWarningMessage() {
      int oldFiles = 0;
      String warning = "";
      String filelist = "";
       File outDir = new File(new File(BASEDIR),OUTDIR);
      
      if (outDir.exists()) {
         File auditpdf = new File(outDir, AUDITLOG_PDF);
         File recountpdf = new File(outDir, RECOUNT_PDF);

         // On confirmation
         if (auditpdf.exists()) {
            oldFiles++;
            filelist += "\""+auditpdf.toString()+"\"\n";
         } 
         if (recountpdf.exists()) {
            oldFiles++;
            filelist += "\""+recountpdf.toString()+"\"\n";
         }
      }
      if (oldFiles > 0) {
        warning = CLEAR_WARNING_MSG_1;
        warning += "\n\nDeze file" + (oldFiles == 1 ? "" : "s") + " verwijderen?\n\n";
        warning += filelist +"\n";
        warning += CLEAR_WARNING_MSG_2;
      } else {
        warning = CLEAR_WARNING_MSG;
      }
      return warning;
   }

  /**
   * Gets called when the clear button is pressed.
   */
  /*@ also
    @ normal_behavior
    @   modifies \everything;
    @   ensures systemIsCleared;
    @*/
  void doAction() {
     clearSystem();
  }

   boolean isDangerousTask() {
      return true;
   }

   boolean isPreStateAllowed(int state) {
      return (state == INIT_STATE);
   }

   int getSuccessState() {
      return CLEARED_STATE;
   }

  /*@ normal_behavior
    @   modifies \everything;
    @   ensures systemIsCleared;
    @*/
  void clearSystem() {
    MenuPanel.getTheMenuPanel().clear();
    AuditLog.clear();
    System.gc();
    // Clear Files
    clearXMLFiles();
    clearTXTFiles();
    clearPDFFiles();
    systemIsCleared = true;
  }
  
  /**
   * Clear the intermediate XML files. Public because they may be called 
   * from anywhere.
   *
   * Static because this method doesn't seem to depend on the state of this
   * object. -- MO
   */
  public static void clearXMLFiles() {
    File outDir = new File(new File(BASEDIR),OUTDIR);
    if (outDir.exists()) {
      String filelist = "";
      
      File auditxml = new File(outDir, AUDITLOG_XML);
      File recountxml = new File(outDir, RECOUNT_XML);

      // Always delete because it's a temporary file...
      auditxml.delete();
      recountxml.delete();
    }
  }

  /**
   * Clear the intermediate TXT files. Public because they may be called 
   * from anywhere.
   */
  public void clearTXTFiles() {
    File outDir = new File(new File(BASEDIR),OUTDIR);
    if (outDir.exists()) {
      String filelist = "";
      
      File decryptedfile = new File(outDir, DECRYPTEDFILE);

      // Always delete because it's a temporary file...
      decryptedfile.delete();
    }
  }

  /**
   * Clear the PDF files. Private because they may not be called 
   * from anywhere.
   */
  private void clearPDFFiles() {
    File outDir = new File(new File(BASEDIR),OUTDIR);
    if (outDir.exists()) {
      String filelist = "";
      
      File auditpdf = new File(outDir, AUDITLOG_PDF);
      File recountpdf = new File(outDir, RECOUNT_PDF);

      // Always delete because confirmation has been given before
      auditpdf.delete();
      recountpdf.delete();
    }
  }
}
