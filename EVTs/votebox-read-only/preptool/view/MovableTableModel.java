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

import java.util.Vector;

import javax.swing.event.TableModelEvent;
import javax.swing.table.DefaultTableModel;

/**
 * An extension of the DefaultTableModel that provides a moveRow method that
 * moves a single row within the table, and fires a special move event that
 * distinguishes from simply updating the objects in each row
 * 
 * @author cshaw
 */
public class MovableTableModel extends DefaultTableModel implements
        IMovableTableModel {

    private static final long serialVersionUID = 1L;

    public MovableTableModel() {
        super();
    }

    public MovableTableModel(int rowCount, int columnCount) {
        super( rowCount, columnCount );
    }

    public MovableTableModel(Object[] columnNames, int rowCount) {
        super( columnNames, rowCount );
    }

    public MovableTableModel(Object[][] data, Object[] columnNames) {
        super( data, columnNames );
    }

    public MovableTableModel(Vector columnNames, int rowCount) {
        super( columnNames, rowCount );
    }

    public MovableTableModel(Vector data, Vector columnNames) {
        super( data, columnNames );
    }

    /**
     * Moves the row from index 'from' to index 'to', and fires a table move
     * event
     * 
     * @param from
     *            the from index
     * @param to
     *            the to index
     */
    @SuppressWarnings("unchecked")
    public void moveRow(int from, int to) {
        if (from != to) {
            Vector row = (Vector) dataVector.get( from );
            if (to > from) {
                for (int i = from; i < to; i++)
                    dataVector.set( i, dataVector.get( i + 1 ) );
            }
            else {
                for (int i = from; i > to; i--)
                    dataVector.set( i, dataVector.get( i - 1 ) );
            }
            dataVector.set( to, row );
        }
        fireTableChanged( new TableModelEvent( this, from, to,
                TableModelEvent.ALL_COLUMNS, MOVE ) );
    }

}
