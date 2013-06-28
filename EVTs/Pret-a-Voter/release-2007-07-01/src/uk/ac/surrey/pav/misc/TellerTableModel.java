package uk.ac.surrey.pav.misc;

import java.util.ArrayList;

import javax.swing.table.AbstractTableModel;

import uk.ac.surrey.pav.entities.Teller;

/**
 * Used to list tellers in a JTable element
 * 
 * @author David Lundin
 *
 */
public class TellerTableModel extends AbstractTableModel {
	
	/**
	 * The tellers that this model sets out
	 */
	ArrayList tellers;
	
	/**
	 * Default constructor
	 * 
	 * @param tellers List of the tellers that the model sets out
	 */
	public TellerTableModel(ArrayList tellers) {
		//Store reference to list
		this.tellers = tellers;
	}

	/**
	 * Returns the number of tellers, or rows, in the table
	 */
	public int getRowCount() {
		//Return the number of tellers
		return this.tellers.size();
	}

	/**
	 * The number of columns in the table
	 */
	public int getColumnCount() {
		//There are 8 columns in this table
		return 8;
	}

	public Object getValueAt(int rowIndex, int columnIndex) {
		//The current teller
		Teller currentTeller = (Teller)this.tellers.get(rowIndex); 
		return null;
	}
	
	

}
