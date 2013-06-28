/*
 * JML specification Copyright 2004 SoS Group, University of Nijmegen
 */

package sos.koa;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import java.util.*;
import javax.swing.*;

/**
 * Class which reacts to buttons in the menu.
 *
 * @version $Id: Task.java,v 1.36 2004/05/29 17:39:57 hubbers Exp $
 *
 * @author Martijn Oostdijk (martijno@cs.kun.nl)
 */
public abstract class Task implements KOAConstants, ActionListener
{
   /** The current sub-task. */
   /*@ spec_public */ int subTaskCount; //@ in objectState;

   /** The (estimated) maximum number of sub-tasks. */
   /*@ spec_public */ int maxSubTasks; //@ in objectState;

   /*@ invariant
     @    0 <= subTaskCount && subTaskCount <= maxSubTasks;
    */

   /** Success status of this task. */
   boolean success; //@ in objectState;

   /** Whether <code>doAction</code> is still running. */
   boolean stillWorking; //@ in objectState;

   /** Progress monitor. */
   ProgressMonitor monitor; //@ in objectState;

   /**
    * Constructs this task.
    */
   Task() {
   }

   /**
    * Indicates whether the user should be warned that we're about to start
    * this task. Default is false.
    *
    * @return By default <code>false</code>.
    */
   /*@ pure */ boolean isDangerousTask() {
      return false;
   }

   /**
    * Indicates whether a progress monitor should be popped up. Default is
    * false.
    *
    * @return By default <code>false</code>.
    */
   /*@ pure */ boolean isProgressMonitoredTask() {
      return false;
   }

   /**
    * Indicates whether this task influences the application's state and whether
    * the GUI should be disabled until this task completes. Default is true.
    *
    * @return By default <code>true</code>.
    */
   /*@ pure */ boolean isModalTask() {
      return true;
   }

   /**
    * Indicates whether the effect of this task can be undone (and whether the
    * user should be given the option to undo the task). Default is false.
    *
    * @return By default <code>false</code>.
    */
   /*@ pure */ boolean isCancelableTask() {
      return false;
   }

   /**
    * Sets the number of already completed subtasks.
    *
    * @param subTaskCount the number of already completed subtasks.
    */
   /*@
     @ normal_behavior
     @ requires subTaskCount >= 0;
     @ requires subTaskCount <= this.maxSubTasks;
     @ assignable objectState;
     @ ensures this.subTaskCount == subTaskCount;
     @*/
   void setSubTaskCount(int subTaskCount) {
      this.subTaskCount = subTaskCount;
   }

   /**
    * Gets information that should be displayed if this task completes
    * successfully.
    *
    * @return information that should be displayed if this task completes
    *    successfully.
    */
   /*@
     @ behavior
     @ assignable AuditLog.*;
     @*/
   String getInfo() {
      return "";
   }

   /**
    * Indicates whether even more information is available about this
    * (completed) task.
    *
    * @return A boolean indicating whether even more information is available
    *    about this (completed) task.
    */
   /*@ pure */ boolean isAdditionalInfoAvailable() {
      return false;
   }

   /**
    * Gets even more information about this (completed) task. The resulting
    * <code>Object</code> can be used in a dialog message.
    *
    * @return Even more information about this (completed) task.
    */
   /*@ pure @*/ Object getAdditionalInfo() {
      return null;
   }

   /**
    * Sets the (estimated) maximum number of sub-tasks.
    *
    * @param maxSubTasks the new (estimated) maximum number of sub-tasks.
    */
   /*@ normal_behavior
     @ requires maxSubTasks >= 0;
     @ requires maxSubTasks >= this.subTaskCount;
     @ assignable objectState;
     @ ensures this.maxSubTasks == maxSubTasks;
    */
   void setMaxSubTasks(int maxSubTasks) {
      this.maxSubTasks = maxSubTasks;
      if (monitor != null) {
         monitor.setMaximum(maxSubTasks);
      }
   }

   /**
    * The title of this task. Is used in title-bar of dialogs.
    *
    * @return Title of this task.
    */
   abstract /*@ pure */ String getTitle();

   /**
    * What to print in success dialog.
    *
    * @return text to print in success dialog.
    */
   abstract /*@ pure */ String getSuccessMessage();

   /**
    * What to print in failure dialog.
    *
    * @return text to print in failure dialog.
    */
   abstract /*@ pure */ String getFailureMessage();

   /**
    * What to print in warning dialog used
    * to ask user if he/she is sure to perform
    * this task.
    *
    * @return text to print in warning dialog.
    */
   /*@ pure */ String getWarningMessage() {
      return "";
   }

   abstract /*@ pure */ boolean isPreStateAllowed(int state);

   /**
    * The application state after successful termination
    * of this task.
    *
    * @return the new state.
    */
   /*@ ensures \result == INIT_STATE ||
     @         \result == CLEARED_STATE ||
     @         \result == CANDIDATES_IMPORTED_STATE ||
     @         \result == VOTES_IMPORTED_STATE ||
     @         \result == PRIVATE_KEY_IMPORTED_STATE ||
     @         \result == PUBLIC_KEY_IMPORTED_STATE ||
     @         \result == VOTES_DECRYPTED_STATE ||
     @         \result == VOTES_COUNTED_STATE ||
     @         \result == REPORT_GENERATED_STATE;
     @*/
   abstract /*@ pure */ int getSuccessState();

   /**
    * Gets called when the button associated to this task
    * is pressed.
    *
    * @param ae Event indicating the button is pressed.
    */
   public void actionPerformed(ActionEvent ae) {
      if (isProgressMonitoredTask()) {
         (new MonitoredThread()).start();
      } else {
         (new ActionThread()).start();
      }
   }

   /**
    * Inner class to monitor the <code>ActionThread</code>.
    */
   class MonitoredThread extends Thread
   {
      /**
       * Runs the MonitoredThread inner class.
       */
      public void run() {
         long initialTime = System.currentTimeMillis();
         subTaskCount = 0;
         monitor =
            new ProgressMonitor(MenuPanel.getTheMenuPanel(),getTitle(),"",0,maxSubTasks);
         monitor.setMillisToPopup(500);
         monitor.setMillisToDecideToPopup(500);
         stillWorking = true;
         (new ActionThread()).start();
         while (stillWorking) {
            long currentTime = System.currentTimeMillis();
            long remainingTime = ((currentTime - initialTime)
                               * (maxSubTasks - subTaskCount))
                               / (subTaskCount + 1);
            monitor.setNote(timeString(remainingTime));
            monitor.setProgress(subTaskCount);
            stillWorking &= !monitor.isCanceled();
            try {
               Thread.sleep(100);
            } catch (InterruptedException ie) {
            }
         }
         if (monitor.isCanceled()) {
            stopAction();
         }
         monitor.close();
      }

      /**
       * A readable <i>hh:mm:ss</i> string representation of
       * <code>time_millis</code>.
       *
       * @param time_millis a time, given in milli-seconds.
       *
       * @return a readable string representation of
       *         <code>time_millis</code>.
       */
      /*@ pure */ String timeString(long time_millis) {
         long time_hours = time_millis / 3600000;
         time_millis %= 3600000;
         long time_minutes = time_millis / 60000;
         time_millis %= 60000;
         long time_seconds = time_millis / 1000;
         String result = "";
         result += Integer.toString((int)time_hours);
         result += ":";
         if (time_minutes < 10) {
            result += "0"+time_minutes;
         } else {
            result += time_minutes;
         }
         result += ":";
         if (time_seconds < 10) {
            result += "0"+time_seconds;
         } else {
            result += time_seconds;
         }
         return result;
      }
   }

   /**
    * Inner class that runs this task's <code>doAction</code>
    * method.
    */
   class ActionThread extends Thread
   {
      /**
       * Runs the <code>ActionThread</code> inner class.
       */
      /*@ also
        @ behavior
        @ assignable \everything;
        @ ensures success ==> MenuPanel.getTheMenuPanel().getState() == getSuccessState();
        @ ensures !success ==> MenuPanel.getTheMenuPanel().getState() == \old(MenuPanel.getTheMenuPanel().getState());
        @*/

      public void run() {
         int preCursorType = MenuPanel.getTheMenuPanel().getCursor().getType();
         String reason = "Onbekende fout!";
         if (isModalTask()) {
            MenuPanel.getTheMenuPanel().setEnabled(false);
         }
         success = false;
         try {
            logStarted();
            if (isDangerousTask()) {
               if (!popupWarning()) {
                  throw new KOAException(TASK_CANCELED_MSG);
               }
            }
            MenuPanel.getTheMenuPanel().setCursor(new Cursor(Cursor.WAIT_CURSOR));
            doAction();
            success = true;
         } catch (KOAException ke) {
            reason = ke.getMessage();
            logFailed(reason);
         } catch (Exception e) {
            reason = e.getMessage();
            logFailed(reason);
            e.printStackTrace();
         } finally {
            stillWorking = false;
            MenuPanel.getTheMenuPanel().setCursor(new Cursor(preCursorType));
            if (isModalTask()) {
               if (success) {
                  if (isCancelableTask()) {
                     if (popupNextOrBack()) {
                        logCompleted();
                        MenuPanel.getTheMenuPanel().setState(getSuccessState());
                        //@ assert MenuPanel.getTheMenuPanel().getState() == \old(MenuPanel.getTheMenuPanel().getState()) + 1;
                     } else {
                        reason = TASK_CANCELED_MSG;
                        logFailed(reason);
                        clear();
                     }
                  } else {
                     popupNext();
                     logCompleted();
                     MenuPanel.getTheMenuPanel().setState(getSuccessState());
                     //@ assert MenuPanel.getTheMenuPanel().getState() == \old(MenuPanel.getTheMenuPanel().getState()) + 1;
                  }
               }
               if (!success) {
                  popupFailure(reason);
                  //@ assert MenuPanel.getTheMenuPanel().getState() == \old(MenuPanel.getTheMenuPanel().getState());
               }
            }
         }
         System.gc();
         MenuPanel.getTheMenuPanel().setEnabled(true);
      }
   }

   /**
    * Performs the actual work of this task.
    *
    * @throws KOAException if something goes wrong.
    */
   /*@
     @ assignable objectState;
     @*/
   abstract void doAction() throws KOAException;

   /**
    * What to do to halt the execution of the <code>doAction</code> method.
    */
   /*@
     @ assignable objectState;
     @*/
   void stopAction() {
   }

   /**
    * Clears temporary memory used by this task.
    */
   /*@
     @ assignable objectState;
     @*/
   void clear() {
   }

   /**
    * Writes a 'task started' entry in the log.
    */
   /*@
     @ assignable AuditLog.*;
     @*/
   void logStarted() {
   }

   /**
    * Writes a 'task canceled' entry in the log.
    */
   /*@
     @ assignable AuditLog.*;
     @*/
   void logCanceled() {
   }

   /**
    * Writes a 'task opened file' entry in the log.
    */
   /*@
     @ assignable AuditLog.*;
     @*/
   void logOpenedFile(File file) {
   }

   /**
    * Writes a 'task failed' entry in the log.
    */
   /*@
     @ assignable AuditLog.*;
     @*/
   void logFailed(String reason) {
   }

   /**
    * Writes a 'task completed' entry in the log.
    */
   void logCompleted() {
   }

   // Pop-up dialogs...

   /**
    * Pops up a dialog.
    */
   /*@ 
     @ assignable AuditLog.*;
     @ assignable MenuPanel.theInstance.currentDir;
     @*/
   File popupGetFile(String extension, String description)
   throws KOAException {
      try {
         File currentDir = MenuPanel.getTheMenuPanel().getCurrentDir();
         JFileChooser chooser = new JFileChooser();
         chooser.setDialogTitle(getTitle());
         chooser.setCurrentDirectory(currentDir);
         chooser.setFileHidingEnabled(false);
         chooser.setFileFilter(new FileNameFilter(extension,description));
         int n = chooser.showOpenDialog(MenuPanel.getTheMenuPanel());
         if (n != JFileChooser.APPROVE_OPTION) {
            throw new KOAException("File selecteren geannuleerd!");
         }
         File file = chooser.getSelectedFile();
         MenuPanel.getTheMenuPanel().setCurrentDir(file.getParentFile());
         logOpenedFile(file);
         return file;
      } catch (KOAException ke) {
         throw new KOAException(ke.getMessage());
      } catch (Exception e) {
         throw new KOAException(DIALOG_ERROR_MSG);
      }
   }

   /**
    * Pops up a dialog.
    */
   /*@ pure @*/ String popupGetPassword() {
      try {
         String result = JOptionPane.showInputDialog(MenuPanel.getTheMenuPanel(),"Geef het password");
         if (result == null) {
            return "";
         }
         return result;
      } catch (Exception e) {
         return "";
      } 
   }

   /**
    * Pops up a dialog.
    */
   /*@
     @ assignable AuditLog.*;
     @*/
   void popupSuccess() {
      try {
         int n = -1;
         if (isAdditionalInfoAvailable()) {
            while (n == -1 || n == MOREINFO_OPTION) {
               n = JOptionPane.showOptionDialog(MenuPanel.getTheMenuPanel(),
                       getSuccessMessage() + "\n\n" + getInfo(),
                       getTitle(),
                       JOptionPane.YES_NO_OPTION,
                       JOptionPane.INFORMATION_MESSAGE,
                       null,
                       OK_MOREINFO_OPTIONS,
                       OK_MOREINFO_OPTIONS[0]);
               if (n == MOREINFO_OPTION) {
                  popupAdditionalInfo();
               }
            }
         } else {
            JOptionPane.showMessageDialog(MenuPanel.getTheMenuPanel(),
               getSuccessMessage() + "\n\n" + getInfo(),
               getTitle(),
               JOptionPane.INFORMATION_MESSAGE);
         }
      } catch (Exception e) {
         e.printStackTrace();
      }
   }

   /**
    * Pops up a dialog.
    */
   /*@ pure @*/ boolean popupWarning() {
      try {
         int n = JOptionPane.showOptionDialog(MenuPanel.getTheMenuPanel(),
                    getWarningMessage(),
                    getTitle(),
                    JOptionPane.YES_NO_OPTION,
                    JOptionPane.QUESTION_MESSAGE,
                    null,
                    YES_CANCEL_OPTIONS,
                    YES_CANCEL_OPTIONS[0]);
         return (n ==  JOptionPane.YES_OPTION);
      } catch (Exception e) {
         return false;
      }
   }

   /**
    * Pops up a dialog.
    */
   /*@
     @ assignable AuditLog.*;
     @*/
   boolean popupNextOrBack() {
      try {
         int n = -1;
         if (isAdditionalInfoAvailable()) {
            while (n == -1 || n == MOREINFO_OPTION || n == LESSINFO_OPTION) {
               n = JOptionPane.showOptionDialog(MenuPanel.getTheMenuPanel(),
                      getSuccessMessage() + "\n\n" + getInfo(),
                      getTitle(),
                      JOptionPane.YES_NO_OPTION,
                      JOptionPane.INFORMATION_MESSAGE,
                      null,
                      OK_MOREINFO_CANCEL_OPTIONS,
                      OK_MOREINFO_CANCEL_OPTIONS[0]);
               if (n == MOREINFO_OPTION) {
                  n = popupAdditionalInfo(OK_LESSINFO_CANCEL_OPTIONS);
               }
            }
         } else {
            n = JOptionPane.showOptionDialog(MenuPanel.getTheMenuPanel(),
                   getSuccessMessage() + "\n\n" + getInfo(),
                   getTitle(),
                   JOptionPane.YES_NO_OPTION,
                   JOptionPane.INFORMATION_MESSAGE,
                   null,
                   OK_CANCEL_OPTIONS,
                   OK_CANCEL_OPTIONS[0]);
         }
         return (n ==  JOptionPane.YES_OPTION);
      } catch (Exception e) {
         return false;
      }
   }

   /**
    * Pops up a dialog.
    */
   /*@
     @ assignable AuditLog.*;
     @*/
   boolean popupNext() {
      try {
         int n = -1;
         if (isAdditionalInfoAvailable()) {
            while (n == -1 || n == MOREINFO_OPTION || n == LESSINFO_OPTION) {
               n = JOptionPane.showOptionDialog(MenuPanel.getTheMenuPanel(),
                      getSuccessMessage() + "\n\n" + getInfo(),
                      getTitle(),
                      JOptionPane.YES_NO_OPTION,
                      JOptionPane.INFORMATION_MESSAGE,
                      null,
                      OK_MOREINFO_OPTIONS,
                      OK_MOREINFO_OPTIONS[0]);
               if (n == MOREINFO_OPTION) {
                  n = popupAdditionalInfo(OK_LESSINFO_OPTIONS);
               }
            }
         } else {
            JOptionPane.showMessageDialog(MenuPanel.getTheMenuPanel(),
               getSuccessMessage() + "\n\n" + getInfo(),
               getTitle(),
               JOptionPane.INFORMATION_MESSAGE);
            n = JOptionPane.YES_OPTION;
         }
         return (n ==  JOptionPane.YES_OPTION);
      } catch (Exception e) {
         return false;
      }
   }

   /**
    * Pops up a dialog.
    */
   /*@ pure @*/ void popupFailure(String info) {
      try {
         JOptionPane.showMessageDialog(MenuPanel.getTheMenuPanel(),
            getFailureMessage() + "\n\n" + info,
            getTitle(),
            JOptionPane.WARNING_MESSAGE);
      } catch (Exception e) {
         e.printStackTrace();
      }
   }

   /**
    * Pops up a dialog.
    */
   /*@ pure @*/ void popupAdditionalInfo() {
      try {
         JOptionPane.showMessageDialog(MenuPanel.getTheMenuPanel(),
            getAdditionalInfo(),
            getTitle(),
            JOptionPane.INFORMATION_MESSAGE);
      } catch (Exception e) {
         e.printStackTrace();
      }
   }

   /**
    * Pops up a dialog.
    */
   /*@ pure @*/ int popupAdditionalInfo(Object[] options) {
      try {
         return
            JOptionPane.showOptionDialog(MenuPanel.getTheMenuPanel(),
               getAdditionalInfo(),
               getTitle(),
               JOptionPane.YES_NO_OPTION,
               JOptionPane.INFORMATION_MESSAGE,
               null,
               options,
               options[0]);
      } catch (Exception e) {
         e.printStackTrace();
         return -1; // In this strange situation we return an int that doesn't
                    // coincide with one of the real options
      }
   }
}

