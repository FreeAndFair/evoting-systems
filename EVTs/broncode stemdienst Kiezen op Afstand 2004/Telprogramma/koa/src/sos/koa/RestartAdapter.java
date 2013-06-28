/*
 * JML specification Copyright 2004 SoS Group, University of Nijmegen
 */

package sos.koa;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;

/**
 * Class to restart the application.
 *
 * @version $Id: RestartAdapter.java,v 1.13 2004/05/21 20:39:37 hubbers Exp $
 *
 * @author Martijn Oostdijk (martijno@cs.kun.nl)
 */
public class RestartAdapter extends Task {

   /**
    * Constructs a new adapter.
    */
   public RestartAdapter() {
   }

   /**
    * Gets the title of this task.
    *
    * @return the title of this task.
    */
   String getTitle() {
      return RESTART_TASK_MSG;
   }

   /**
    * What to print in success dialog.
    *
    * @return text to print in success dialog.
    */
   String getSuccessMessage() {
      return RESTART_SUCCESS_MSG;
   }

   /**
    * What to print in failure dialog.
    *
    * @return text to print in failure dialog.
    */
   String getFailureMessage() {
      return RESTART_FAILURE_MSG;
   }

   /**
    * What to print in warning dialog used
    * to ask user if he/she is sure to perform
    * this task.
    *
    * @return text to print in warning dialog.
    */
   String getWarningMessage() {
      return RESTART_WARNING_MSG;
   }

   /**
    * Indicates whether the user should be warned that we're about to start
    * this task. Restarting is dangerous, so returns <code>true</code>.
    *
    * @return restarting is dangerous, so <code>true</code>.
    */
   boolean isDangerousTask() {
      return true;
   }

   /**
    * Performs the actual work of this task.
    *
    * @throws KOAException if something goes wrong.
    */
   /*@ pure @*/ void doAction() {
      // Do nothing, restarting only affects the state.
   }

   /*@ pure */ boolean isPreStateAllowed(int state) {
      return true;
   }

   /**
    * The application state after successful termination of this task.
    * After restarting the state should be <code>INIT_STATE</code>.
    *
    * @return the initial state.
    */
   int getSuccessState() {
      return INIT_STATE;
   }
}

