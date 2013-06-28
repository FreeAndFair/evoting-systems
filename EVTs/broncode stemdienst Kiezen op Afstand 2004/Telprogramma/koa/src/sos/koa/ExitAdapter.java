/*
 * JML specification Copyright 2004 SoS Group, University of Nijmegen
 */

package sos.koa;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;

/**
 * Class to close this application.
 * This closes the application for example when the window is closed.
 *
 * @version $Id: ExitAdapter.java,v 1.17 2004/05/18 12:44:54 hubbers Exp $
 *
 * @author Martijn Oostdijk (martijno@cs.kun.nl)
 */
public class ExitAdapter extends Task implements WindowListener
{
   /**
    * Constructs this adapter.
    */
   public ExitAdapter() {
   }

   String getTitle() {
      return EXIT_TASK_MSG;
   }

   String getSuccessMessage() {
      return EXIT_SUCCESS_MSG;
   }

   String getFailureMessage() {
      return EXIT_FAILURE_MSG;
   }

   String getWarningMessage() {
      return EXIT_WARNING_MSG;
   }

   /*@ pure */ boolean isPreStateAllowed(int state) {
      return true;
   }

   int getSuccessState() {
      return INIT_STATE;
   }

   public void windowActivated(WindowEvent e) {
   }

   public void windowClosed(WindowEvent e) {
   }

   /**
    * Gets called when the user closes this application's window.
    *
    * @param e Event indicating the window is closing.
    */
   public void windowClosing(WindowEvent e) {
      exit(0);
   }

   /**
    * This method is here since we implement <code>WindowListener</code>.
    *
    * @param e a window event.
    */
   public void windowDeactivated(WindowEvent e) {
   }

   /**
    * This method is here since we implement <code>WindowListener</code>.
    *
    * @param e a window event.
    */
   public void windowDeiconified(WindowEvent e) {
   }

   /**
    * This method is here since we implement <code>WindowListener</code>.
    *
    * @param e a window event.
    */
   public void windowIconified(WindowEvent e) {
   }

   /**
    * This method is here since we implement <code>WindowListener</code>.
    *
    * @param e a window event.
    */
   public void windowOpened(WindowEvent e) {
   }

   boolean isDangerousTask() {
      return true;
   }

   /**
    * Clears the temporary XML files and exits.
    */
   /*@
     @ also
     @ assignable objectState;
     @*/
   public void doAction() {
      ClearAdapter.clearXMLFiles();
      exit(0);
   }

   /**
    * Exits the application with status code <code>status</code>.
    *
    * @param status the status code.
    */
   /*@
     @ assignable objectState;
     @*/
   void exit(int status) {
      System.exit(status);
   }
}

