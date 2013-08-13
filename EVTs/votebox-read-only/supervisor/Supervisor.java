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

package supervisor;

import javax.swing.JOptionPane;

import supervisor.model.Model;
import supervisor.view.View;
import auditorium.Bugout;
import votebox.AuditoriumParams;

/**
 * This is the main entry point of the Supervisor. It is the "Controller" of the
 * MVC pattern.
 * @author cshaw
 */
public class Supervisor {

    public static final String FONTNAME = "Sans";

    /**
     * Runs the supervisor. If an argument is given, it will be the serial
     * number, otherwise, a random number between 1 and 9 is chosen.
     * @param args
     */
    public static void main(String[] args) {
		int i = 0;


		if (args.length > i && args[i].equals("-q")) {
			Bugout.MSG_OUTPUT_ON = false;
			i++;
		}

        if (args.length > i)
            new Supervisor(Integer.parseInt(args[i]));
        else
            new Supervisor(-1);
    }

    private Model model;

    private View view;

    /**
     * Constructs (and starts) a new instance of a supervisor
     * @param serial
     */
    private Supervisor(int serial) {
    	if(serial != -1)
    		model = new Model(serial, new AuditoriumParams("supervisor.conf"));
    	else
    		model = new Model(new AuditoriumParams("supervisor.conf"));
    	
        view = new View(model);
        view.setVisible(true);

        String keyword = "";
        while (keyword == null || keyword.equals(""))
            keyword = JOptionPane.showInputDialog(view,
                    "Please enter today's election keyword:", "Keyword",
                    JOptionPane.QUESTION_MESSAGE);
        model.setKeyword(keyword);

        view.display();
        model.start();
    }
}
