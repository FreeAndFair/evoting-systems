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

package preptool.controller;

import preptool.model.*;
import preptool.view.*;

/**
 * The Controller is main entry point of the program that initializes the model,
 * view and creates the adapters necesarry for communication between the model
 * and view
 * 
 * @author cshaw
 */
public class Controller {

    /**
     * The model of the program
     */
    private Model model;

    /**
     * The view (or GUI) of the program
     */
    private View view;

    /**
     * Constructs a new Controller. Initializes the model, view, and links them
     * with the model adapter. Finally it sets the view to visible.
     */
    public Controller() {
        ThreadGroup exceptionThreadGroup = new ExceptionGroup();
        new Thread( exceptionThreadGroup, "Init thread" ) {
            public void run() {
                model = new Model();
                view = new View( model );
                view.setVisible( true );
            }
        }.start();
    }

    /**
     * The main method of the program, constructs a new Contoller
     * 
     * @param args
     *            not used
     */
    public static void main(String args[]) {
        new Controller();
    }

}
