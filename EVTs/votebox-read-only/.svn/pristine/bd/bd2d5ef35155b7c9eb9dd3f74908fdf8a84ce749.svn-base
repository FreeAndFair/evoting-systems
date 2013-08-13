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

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

/**
 * Log's job is to serialize messages that are heard over auditorium. In
 * addition, the log keeps data structures around that allow it to quickly
 * compute whether or not a given s-expression has been heard before, as well as
 * keep track of what the most recently heard but not pointed to messages are.
 * (This is useful for helping the temporal layer decide what messages should be
 * pointed to when said messages are being constructed.)
 * 
 * @author derrley
 */
public class Log {

    private final FileOutputStream _location;
    private final HashSet<MessagePointer> _haveSeen;
    private final LinkedList<MessagePointer> _last;

    /**
     * Construct a Log instance that serializes log data to a given location.
     * 
     * @param location
     *            This is the location that should be written to.
     * @throws FileNotFoundException
     *             This method throws if the given location cannot be found.
     */
    public Log(File location) throws FileNotFoundException {
        _location = new FileOutputStream( location );
        _haveSeen = new HashSet<MessagePointer>();
        _last = new LinkedList<MessagePointer>();
    }

    /**
     * Call this method to check and see if a message has been seen before, and
     * if it has not, log it.
     * 
     * @param message
     *            This is the message in question. Log it if it hasn't been seen
     *            before.
     * @return This method returns true if something new gets added to the log,
     *         and false otherwise.
     * @throws IOException
     *             This method throws if there is an IO error when trying to add
     *             the message to the log file on disk.
     */
    public boolean logAnnouncement(Message message) throws IOException {
        MessagePointer tomessage = new MessagePointer( message );
        if (!_haveSeen.contains( tomessage )) {
            _haveSeen.add( tomessage );
            _last.add( tomessage );
            write( message );
            return true;
        }
        return false;
    }

    /**
     * Add a message to the "last" list. This message will be included in the
     * pointer set for the next message sent out.
     * 
     * @param message
     *            Add this message.
     */
    public void updateLast(MessagePointer message) {
        _last.add( message );
    }

    /**
     * Remove a pointer from the last list, if it exists in the list.
     * 
     * @param message
     *            Remove this message from the last list.
     */
    public void removeFromLast(MessagePointer message) {
        _last.remove( message );
    }

    /**
     * Get a list of messages that have been seen but not yet referenced.
     * Calling this method effectively clears the last list (before saving it as
     * a return value).
     * 
     * @return This method returns the last list.
     */
    public MessagePointer[] getLast() {
        MessagePointer[] ret = _last.toArray( new MessagePointer[0] );
        _last.clear();
        return ret;
    }

    private void write(Message message) throws IOException {
        _location.write( message.toASE().toVerbatim() );
        _location.flush();
    }

    // ** Testing Methods ***
    /**
     * THIS METHOD IS ONLY USED FOR TESTING. Use the return value of
     * logAnnouncement to know whether or not you've seen a message (becaues the
     * lookup is done atomically with the store!)
     */
    public synchronized HashSet<MessagePointer> TESTgetSetCopy() {
        return new HashSet<MessagePointer>( _haveSeen );
    }

    /**
     * THIS METHOD IS ONLY USED FOR TESTING. Use getLast() in practice, because
     * it gets the last set and then subsequently clears it in one atomic
     * operation.
     */
    public synchronized List<MessagePointer> TESTgetLast() {
        return new LinkedList<MessagePointer>( _last );
    }
}
