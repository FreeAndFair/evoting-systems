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

package auditorium.test;

import java.io.File;
import java.io.FileInputStream;

import auditorium.HostPointer;
import auditorium.MessagePointer;

import sexpression.*;
import sexpression.stream.*;

public class PointerExtractor {

    // 0: id
    // 1: ip
    // 2: port
    // 3: sequence
    // 4: cert
    // 5: signature
    // 6: list-of-pointers
    // 7: datum
    public static final ASExpression PATTERN = new ListExpression(
            StringExpression.makeString( "announce" ), HostPointer.PATTERN,
            new ListExpression( StringExpression.makeString( "sequence" ),
                    StringWildcard.SINGLETON, new ListExpression(
                            StringExpression.makeString( "signature" ),
                            StringWildcard.SINGLETON, StringWildcard.SINGLETON,
                            new ListExpression( StringExpression
                                    .makeString( "succeeds" ),
                                    new ListWildcard( MessagePointer.PATTERN ),
                                    Wildcard.SINGLETON ) ) ) );

    private final String _path;

    public PointerExtractor(String path) {
        _path = path;
    }

    public void extract() throws Exception {
        ASEInputStreamReader reader = new ASEInputStreamReader(
                new FileInputStream( new File( _path ) ) );

        ASExpression read;
        while ((read = reader.read()) != null) {
            try {
                ListExpression result = (ListExpression) PATTERN.match( read );
                System.out.println( "ID:" + result.get( 0 ) + " SEQUENCE:"
                        + result.get( 3 ) + " MESSAGE:" + result.get( 7 ) );
                System.err.println( "Pointers:" );
                for (ASExpression ase : (ListExpression) result.get( 6 )) {
                    ListExpression le = (ListExpression) ase;
                    System.err.println( "    " + le.get( 1 ) + " / "
                            + le.get( 2 ) );
                }
            }
            catch (ClassCastException e) {
                System.err.println( "Skipping malformed expression" );
            }
        }
    }

    public static void main(String[] args) {
        System.out.println( "Reading files" );
        for (String s : args)
            try {
                new PointerExtractor( s ).extract();
            }
            catch (Exception e) {
                System.err.println( e );
            }
    }
}
