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

package votebox.middle.datacollection;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.util.Date;
import java.util.LinkedList;
import java.util.List;

import sexpression.*;
import sexpression.stream.*;

/**
 * A data logger is a simple wrapper around an s-expression output writer. It
 * offers a few added benefits:<br>
 * 1) Every expression that gets written to disk needs to be in the form (UID
 * Type Event Timestamp) and this class will guarentee that only entries of this
 * type are written down in the log.<br>
 * 2) In order to accmplish #1, this class offeres a nice interface (a method
 * definition) which eliminates the need for an outside user to even ever
 * construct an ASExpression.<br>
 * <br>
 * This module is to be used with human factors testing only. This is not to be
 * confused with the module that does redundant event logging over a network.
 * 
 * 
 * @author Kyle
 * 
 */
public class DataLogger {

    /**
     * Singleton Design Pattern.
     */
    private static DataLogger Singleton = null;

    /**
     * All s-expressions that claim to be log entries need to match this
     * template.
     */
    private static final ASExpression Template = new ListExpression(
            StringWildcard.SINGLETON, StringWildcard.SINGLETON,
            StringWildcard.SINGLETON, StringWildcard.SINGLETON );

    /**
     * This is the writer that will do the actual dumping of s-expressions.
     */
    private ASEWriter _writer;

    /**
     * These are the entries that didn't get logged because of reasons beyond
     * our control.
     */
    private List<ASExpression> _unloggedEntries = new LinkedList<ASExpression>();

    /**
     * Use this field to dump cast ballot information.
     */
    private ASEWriter _ballotwriter;

    /**
     * This isthe public constructor to DataLogger
     * 
     * @param filename
     *            This is the filename of the file where the logs needs to go.
     * 
     */
    private DataLogger(File filename) {
        try {
            if (filename.exists())
                filename = new File( filename.getName() + "_" );

            _writer = new ASEWriter( new FileOutputStream( filename ) );
            _ballotwriter = new ASEWriter( new FileOutputStream( filename
                    + "_ballot" ) );
        }
        catch (FileNotFoundException e) {
            // This shouldn't really ever happen...
            e.printStackTrace();
            throw new RuntimeException(
                    "DataLogger instantiation failed for filesystem reasons." );
        }
    }

    public static void CreateAndDump(String UID, String type, String event,
            Date timestamp) {
        if (Singleton == null)
            return;
        Singleton.createAndDump( UID, type, event, timestamp );
    }

    public static void DumpBallot(ASExpression ballot) {
        if (Singleton == null){
        	System.out.println("Cancelled dumping ballot, [Singleton = null]");
            return;
        }//if
        Singleton.dumpBallot( ballot );
    }

    /**
     * Init/Change the filename that this DataLogger is logging to. This method
     * must be called before dump(...)
     * 
     * @param filename
     *            This is the filename that this data logger is to log to.
     */
    public static void init(File filename) {
        Singleton = new DataLogger( filename );
    }

    /**
     * Call this method to actually dump an s-expression to the log file. If
     * there is an error, the given s-expression will be saved for later
     * retrieval from getUnloggedMessages().
     * 
     * @param log
     *            This is the log entry that actually needs to be dumped to the
     *            log file. This log file must match the template (String String
     *            String String)
     */
    private void dump(ASExpression log) {
        try {
            if (Template.match( log ) != NoMatch.SINGLETON)
                _writer.writeASE( log );
        }
        catch (UnsupportedEncodingException e) {
            // Encoding errors should actually stop things because this is a
            // serious problem if we're relying on this module.
            e.printStackTrace();
            throw new RuntimeException(
                    "DataLogger dump failed becaues of an unsupported encoding error." );
        }
        catch (IOException e) {
            // IO errors shouldn't stop the process of things, but we need
            // to make sure that keep the expressions that don't get logged
            // so that if the disk is failing, the logged entries can be
            // manually taken down after the program closes.
            _unloggedEntries.add( log );
        }
    }

    /**
     * Call this method to create a log file entry (an s-expression) and log it
     * to disk. This method creates an s-expression that looks like (UID, type,
     * event, timestamp) with the members of this list given by the parameters
     * of this method.
     * 
     * @param UID
     *            This should be the UID of the control that is generating this
     *            event.
     * @param type
     *            This is the type of control (IE ToggleButton or Button)
     * @param event
     *            This is the type of even that is being logged (selected or
     *            deselected)
     * @param timestamp
     *            This is a timestamp of when the event occurred locally.
     */
    private void createAndDump(String UID, String type, String event,
            Date timestamp) {
        dump( new ListExpression( StringExpression.makeString( UID ),
                StringExpression.makeString( type ), StringExpression
                        .makeString( event ), StringExpression.makeString( Long
                        .toString( timestamp.getTime() ) ) ) );
    }

    /**
     * Dump the ballot to disk.
     * 
     * @param ballot
     */
    private void dumpBallot(ASExpression ballot) {
        try {
            _ballotwriter.writeASE( ballot );
            System.out.println("Successfully dumped ballot to file.");
        }
        catch (UnsupportedEncodingException e) {
            // Encoding errors should actually stop things because this is a
            // serious problem if we're relying on this module.
            e.printStackTrace();
            throw new RuntimeException(
                    "DataLogger dump failed becaues of an unsupported encoding error." );
        }
        catch (IOException e) {
        	System.out.println("\"Recoverable\" error encountered...");
        	e.printStackTrace();
        	
            // IO errors shouldn't stop the process of things, but we need
            // to make sure that keep the expressions that don't get logged
            // so that if the disk is failing, the logged entries can be
            // manually taken down after the program closes.
            _unloggedEntries.add( ballot );
        }
    }
}
