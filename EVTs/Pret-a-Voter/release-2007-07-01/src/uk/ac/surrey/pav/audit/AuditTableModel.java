package uk.ac.surrey.pav.audit;

import java.util.ArrayList;

import javax.swing.table.AbstractTableModel;

/**
 * Table model which displays information about the audit
 * 
 * @author David Lundin
 *
 */
public class AuditTableModel extends AbstractTableModel {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The column headers
	 */
	private String[] columnHeaders = {"Timestamp", "Action", "Result"};
	
	/**
	 * An arraylist of the rows in the table
	 */
	private ArrayList rows = new ArrayList();
	
	/**
	 * The number of columns
	 */
	public int getColumnCount() {
		return this.columnHeaders.length;
	}

	/**
	 * The number of rows
	 */
	public int getRowCount() {
		return this.rows.size();
	}

	/**
	 * The value in a particular cell
	 */
	public Object getValueAt(int y, int x) {
		
		return ((AuditTableRow)this.rows.get(y)).getCol(x);
		
	}
	
	public void addRow(String action, String result) {
		
		this.rows.add(new AuditTableRow(action, result));
		this.fireTableRowsInserted(0, 0);
		
	}

	public String getColumnName(int col) {
		return this.columnHeaders[col];
	}

}
