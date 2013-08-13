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

package auditorium;

import java.io.OutputStream;
import java.io.PrintWriter;

/**
 * This class contains debugging output messages (which might, someday, get
 * turned into logs).
 * 
 * @author kyle
 * 
 */
public class Bugout {

    /**
     * Clear this field to disable debugging messages.
     */
    public static volatile boolean MSG_OUTPUT_ON = true;

    /**
     * Clear this field to disable error output.
     */
    public static volatile boolean ERR_OUTPUT_ON = true;

    /**
     * Set where the debugging and error message go.
     * 
     * @param msg
     *            Normal debugging messages go here.
     * @param err
     *            Error messages go here.
     */
    public static void changeStreams(OutputStream msg, OutputStream err) {
        _msg = new PrintWriter( msg );
        _err = new PrintWriter( err );
    }

    private static PrintWriter _msg = new PrintWriter( System.out );
    private static PrintWriter _err = new PrintWriter( System.err );

    /**
     * Print a debugging message.
     * 
     * @param message
     *            Print this message.
     */
    public synchronized static void msg(String message) {
        if (MSG_OUTPUT_ON)
            _msg.println( "MESSAGE: " + message );
        _msg.flush();
    }

    /**
     * Print an error message.
     * 
     * @param err
     *            Print this message.
     */
    public synchronized static void err(String err) {
        if (ERR_OUTPUT_ON)
            _err.println( "ERROR: " + err );
        _err.flush();
    }

}
