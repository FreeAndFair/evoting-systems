/**
  * This file is part of VoteBox.
  * 
  * VoteBox is free software: you can redistribute it and/or modify
  * it under the terms of the GNU General Public License version 3 as published by
  * the Free Software Foundation.
  * 
  * You should have received a copy of the GNU General Public License
  * along with VoteBox, found in the root of any distribution or
  * repository containing all or part of VoteBox.
  * 
  * THIS SOFTWARE IS PROVIDED BY WILLIAM MARSH RICE UNIVERSITY, HOUSTON,
  * TX AND IS PROVIDED 'AS IS' AND WITHOUT ANY EXPRESS, IMPLIED OR
  * STATUTORY WARRANTIES, INCLUDING, BUT NOT LIMITED TO, WARRANTIES OF
  * ACCURACY, COMPLETENESS, AND NONINFRINGEMENT.  THE SOFTWARE USER SHALL
  * INDEMNIFY, DEFEND AND HOLD HARMLESS RICE UNIVERSITY AND ITS FACULTY,
  * STAFF AND STUDENTS FROM ANY AND ALL CLAIMS, ACTIONS, DAMAGES, LOSSES,
  * LIABILITIES, COSTS AND EXPENSES, INCLUDING ATTORNEYS' FEES AND COURT
  * COSTS, DIRECTLY OR INDIRECTLY ARISING OUR OF OR IN CONNECTION WITH
  * ACCESS OR USE OF THE SOFTWARE.
 */

package preptool.view;

import java.util.Observable;

/**
 * A class that contains task names and progress values of an asynchronous task.
 * Observers (such as a ProgressDialog) can receive updates of the progress.
 * @author cshaw
 */
public class ProgressInfo extends Observable {

    private volatile int taskProgress;

    private volatile String subTaskName;

    private volatile int subTaskProgress;

    private volatile String subSubTaskName;

    private volatile boolean cancelled;

    private volatile boolean finished;

    private volatile int numTasks;

    private volatile int currentTask;

    /**
     * Constructs a new ProgressInfo class, with default values
     */
    public ProgressInfo() {
        taskProgress = 0;
        subTaskName = "Initializing";
        subTaskProgress = 0;
        subSubTaskName = "Initializing";
        currentTask = 0;
        numTasks = 1;
        cancelled = false;
        finished = false;
    }

    /**
     * Cancels the task
     */
    public void cancel() {
        cancelled = true;
        setChanged();
        notifyObservers();
    }

    /**
     * Notifies the progress info that the task is finished
     */
    public void finished() {
        finished = true;
        setChanged();
        notifyObservers();
    }

    /**
     * Returns the current sub-sub task name
     */
    public String getSubSubTaskName() {
        return subSubTaskName;
    }

    /**
     * Returns the current sub task name
     */
    public String getSubTaskName() {
        return subTaskName;
    }

    /**
     * Returns the current sub task progress
     */
    public int getSubTaskProgress() {
        return subTaskProgress;
    }

    /**
     * Returns the current task progress
     */
    public int getTaskProgress() {
        return taskProgress;
    }

    /**
     * Returns whether this task is cancelled
     */
    public boolean isCancelled() {
        return cancelled;
    }

    /**
     * Returns whether this task is finished
     */
    public boolean isFinished() {
        return finished;
    }

    /**
     * Sets the current task
     */
    public void setCurrentTask(String subTask, int taskNum) {
        subTaskName = subTask;
        currentTask = taskNum;
        calculate();
    }

    /**
     * Sets the number of tasks
     */
    public void setNumTasks(int numTasks) {
        this.numTasks = numTasks;
        calculate();
    }

    /**
     * Sets the progress to the given task names and progress values
     */
    public void setProgress(String subSubTask, int subTaskProg) {
        subSubTaskName = subSubTask;
        subTaskProgress = subTaskProg;
        calculate();
    }

    private void calculate() {
        taskProgress = (currentTask * 100 + subTaskProgress) / numTasks;
        setChanged();
        notifyObservers();
    }

}
