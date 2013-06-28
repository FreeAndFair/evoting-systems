package uk.ac.surrey.pav.ballotform;

import java.util.ArrayList;
import java.util.Collections;

public class TellerInternalBatch {

	/**
	 * A list of all the rows in the batch
	 */
	private ArrayList rows = new ArrayList();
	
	/**
	 * This is a TellerBatch based on the contents in this batch
	 */
	private TellerBatch tellerBatch;
	
	/**
	 * Constructor
	 *
	 */
	public TellerInternalBatch() {
		
		//Create a teller batch object that can be used later
		this.tellerBatch = new TellerBatch();
		
	}
	
	/**
	 * Adds a row to the batch
	 * 
	 * @param row TellerInternalBatchRow object to add to list
	 */
	public void addRow(TellerInternalBatchRow row) {

		//Update the sort index on the row to the next incremented
		row.setSortIndex(this.rows.size());
		
		//Store the TellerInternalBatchRow object
		this.rows.add(row);
		
		//Also store reference to the PartialForm in the TellerBatch object
		this.tellerBatch.addBallotForm(row.partialForm);
		
	}
	
	/**
	 * The number of rows in the batch
	 * 
	 * @return The number of rows
	 */
	public int getNumberOfRows() {
		return this.rows.size();
	}
	
	/**
	 * Returns a specific row
	 * 
	 * @param x The index of the row
	 * @return TellerInternalBatchRow
	 */
	public TellerInternalBatchRow getRow(int x) {
		return (TellerInternalBatchRow)this.rows.get(x);
	}
	
	/**
	 * Returns a teller batch based on this internal batch
	 * 
	 * @return TellerBatch object
	 */
	public TellerBatch getTellerBatch() {
		return this.tellerBatch;
	}
	
	/**
	 * Sorts the rows in order of onion value
	 *
	 */
	public void sort() {
		Collections.sort(this.rows);
	}
	
}
