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

package auditorium.loganalysis;

import java.io.CharArrayReader;
import java.io.EOFException;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;

import auditorium.*;

import sexpression.*;
import sexpression.lexer.*;
import sexpression.parser.*;
import sexpression.stream.*;

/**
 * Builds a representation of the dag of logs based on the auditorium file
 * format. The dag doesn't actually contain the messages, only pointers to them.
 * 
 * @author kyle
 * 
 */
public class Dag {

    public static final ASExpression PATTERN = new Parser(
            new Lexer(
                    new CharArrayReader(
                            new String(
                                    "(announce(host #string #string #string) #string (signed-message (cert (signature #string #string (key #string #string #string #string)))(signature #string #string (succeeds #list:(ptr #string #string #string) #any))))" )
                                    .toCharArray() ) ) ).read();

    private final String _filename;
    private final HashMap<MessagePointer, ArrayList<MessagePointer>> _dag;

    /**
     * @param filename
     *            Build the dag from an auditorium log file found at this path.
     */
    public Dag(String filename) {
        _filename = filename;
        _dag = new HashMap<MessagePointer, ArrayList<MessagePointer>>();
    }

    /**
     * Parse the file given at construct time and build the dag based on this
     * file.
     */
    public void build() throws IOException, InvalidVerbatimStreamException,
            IncorrectFormatException {
        ASEInputStreamReader reader = new ASEInputStreamReader(
                new FileInputStream( new File( _filename ) ) );

        try {
            while (true) {
                ASExpression message = reader.read();
                MessagePointer ptr = new MessagePointer( new Message( message ) );

                ArrayList<MessagePointer> predlist = new ArrayList<MessagePointer>();
                ListExpression matchresult = (ListExpression) PATTERN
                        .match( message );
                for (ASExpression ase : (ListExpression) matchresult.get( 12 ))
                    predlist.add( new MessagePointer( ase ) );
                _dag.put( ptr, predlist );
            }
        }
        catch (EOFException e) {}
    }

    /**
     * @return This method returns the dag structure that is wrapped by this
     *         instance.
     */
    public HashMap<MessagePointer, ArrayList<MessagePointer>> getDag() {
        return _dag;
    }

    /**
     * Query the dag for information about branch rates.
     * 
     * @return This method returns a map which represents the histogram of
     *         branch rates: rate->number (where rate is number of succeeds
     *         pointers and number is how many messages had this given number of
     *         pointers).
     */
    public HashMap<Integer, Integer> getBranchStatistics() {
        HashMap<Integer, Integer> ret = new HashMap<Integer, Integer>();
        for (MessagePointer mp : _dag.keySet()) {
            int num = _dag.get( mp ).size();
            if (ret.containsKey( num ))
                ret.put( num, ret.get( num ) + 1 );
            else
                ret.put( num, 1 );
        }
        return ret;
    }
}
