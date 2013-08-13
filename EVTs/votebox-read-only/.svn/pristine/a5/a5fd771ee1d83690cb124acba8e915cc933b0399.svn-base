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

package supervisor.model;

/**
 * The model of a supervisor machine on the network.
 * @author cshaw
 */
public class SupervisorMachine extends AMachine {

    /**
     * Represents a supervisor that is active
     */
    public static final int ACTIVE = 4;

    /**
     * Represents a supervisor that is inactive
     */
    public static final int INACTIVE = 5;

    private boolean currentMachine;

    /**
     * Constructs a new supervisor machine
     * @param serial the serial number of the supervisor
     * @param current whether the supervisor is the current machine
     */
    public SupervisorMachine(int serial, boolean current) {
        super(serial);
        this.currentMachine = current;
    }

    /**
     * @return whether this is the current machine
     */
    public boolean isCurrentMachine() {
        return currentMachine;
    }

}
