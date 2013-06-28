package uk.ac.surrey.pav.bulletinboard.tablemodels;

import javax.swing.table.AbstractTableModel;

import uk.ac.surrey.pav.bulletinboard.entities.Candidate;
import uk.ac.surrey.pav.bulletinboard.events.TallyUpdatedEvent;
import uk.ac.surrey.pav.bulletinboard.events.TallyUpdatedListener;
import uk.ac.surrey.pav.bulletinboard.tally.Tally;
import uk.ac.surrey.pav.bulletinboard.tally.TallyRound;

/**
 * Displays the tally list
 * 
 * @author David Lundin
 *
 */
public class TallyTableModel extends AbstractTableModel implements TallyUpdatedListener {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	/**
	 * The tally that is being set out
	 */
	private Tally tally;
	
	/**
	 * Constructor
	 * 
	 * @param tally
	 */
	public TallyTableModel(Tally tally) {
		//Store reference to the tally
		this.tally = tally;
		
		//Listen to changes
		this.tally.addTallyUpdatedListener(this);
	}

	/**
	 * Receive the TallyUpdatedEvent event
	 */
	public void receiveTallyUpdatedEvent(TallyUpdatedEvent event) {
		//Fire an event to update the table
		this.fireTableStructureChanged();
	}

	/**
	 * The number of rows in the table
	 */
	public int getRowCount() {
		return this.tally.race.candidates.size() + 2;
	}

	/**
	 * Returns the number of columns in the table
	 */
	public int getColumnCount() {
		return this.tally.rounds.size() + 1;
	}

	/**
	 * Returns the value in a particular cell
	 */
	public Object getValueAt(int rowIndex, int columnIndex) {
		
		//Check if candidate name or value of a tally round
		if(columnIndex == 0) {
			if(rowIndex < this.tally.race.candidates.size()) {
				return ((Candidate)this.tally.race.candidates.get(rowIndex)).name;
			} else if(rowIndex == this.tally.race.candidates.size()) {
				return "(discarded)";
			} else {
				return null;
			}
		} else {
			if(rowIndex < this.tally.race.candidates.size()) {
				int currentScore = ((TallyRound)this.tally.rounds.get(columnIndex-1)).scores[rowIndex];
				if(currentScore >= 0) {
					return "" + currentScore;
				} else {
					return "Eliminated";
				}
			} else if(rowIndex == this.tally.race.candidates.size()) {
				return "" + ((TallyRound)this.tally.rounds.get(columnIndex-1)).discarded;
			} else {
				return ((TallyRound)this.tally.rounds.get(columnIndex-1)).description;
			}
		}
		
	}

	/**
	 * Returns the name of a column
	 */
	public String getColumnName(int col) {
		if(col == 0) {
			return "Candidate";
		} else {
			return ((TallyRound)this.tally.rounds.get(col-1)).name;
		}
	}

}
