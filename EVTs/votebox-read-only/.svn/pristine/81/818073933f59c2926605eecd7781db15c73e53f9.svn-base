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

package votebox.middle;

/**
 * An object that implements IGlobalVars knows all the neccesary path and
 * filename information for a single ballot.
 * 
 * @author Kyle
 * 
 */
public interface IBallotVars {

    /**
     * Invoke this method to get the root path to all ballot related
     * information.
     * 
     * @return This method returns the ballot path.
     */
    String getBallotPath();

    /**
     * Invoke this method to get the fully qualified path+filename of the ballot
     * XML file.
     * 
     * @return This method returns the ballot file path.
     */
    String getBallotFile();

    /**
     * Invoke this method to get the fully qualified path+filename of the ballot
     * schema XML file.
     * 
     * @return This method returns the ballot schema file path.
     */
    java.net.URL getBallotSchema();

    /**
     * Invoke this method to get the fully qualified path+filename of the layout
     * XML file.
     * 
     * @return This method returns the layout file path.
     */
    String getLayoutFile();

    /**
     * Invoke this method to get the fully qualified path+filename of the layout
     * schema XML file.
     * 
     * @return This method returns the layout schema path.
     */
    java.net.URL getLayoutSchema();
}
