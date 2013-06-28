package uk.ac.surrey.pav.bulletinboard.tablemodels;

import javax.swing.table.AbstractTableModel;

import sun.misc.BASE64Encoder;
import uk.ac.surrey.pav.bulletinboard.BulletinBoard;
import uk.ac.surrey.pav.bulletinboard.challenges.Challenge;
import uk.ac.surrey.pav.bulletinboard.entities.Race;
import uk.ac.surrey.pav.bulletinboard.events.RaceUpdatedEvent;
import uk.ac.surrey.pav.bulletinboard.events.RaceUpdatedListener;

/**
 * Displays the challenge table
 * 
 * @author David Lundin
 *
 */
public class ChallengeTableModel extends AbstractTableModel implements RaceUpdatedListener {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The race that we are setting out in the window now
	 */
	private Race race;
	
	/**
	 * The bulletin board
	 */
	private BulletinBoard bulletinBoard;

	/**
	 * A Base64 encoder used to set out byte[] on screen 
	 */
	BASE64Encoder encoder = new BASE64Encoder();

	/**
	 * Constructor
	 *
	 */
	public ChallengeTableModel(BulletinBoard bulletinBoard, Race race) {
		//Store refereces
		this.bulletinBoard = bulletinBoard;
		this.race = race;
		
		//Register to listen for updates of the race
		this.race.addRaceUpdatedListener(this);
	}
	
	public void receiveRaceUpdatedEvent(RaceUpdatedEvent event) {
		//Fire an event to update the table
		this.fireTableStructureChanged();
	}

	public int getRowCount() {
		//There are always three rows: random, commitment and value
		return 4;
	}

	public int getColumnCount() {
		//There are the number of tellers + one number of columns
		return this.bulletinBoard.getTellerCount() + 1;
	}

	public Object getValueAt(int rowIndex, int columnIndex) {
		
		if(columnIndex == 0) {
			
			//Row headers
			switch(rowIndex) {
			case 1:
				return "Commitment";
			case 2:
				return "Teller Nonce";
			case 3:
				return "Value";
			default:
				return "Bulletinboard Nonce";
			}

		} else {
			
			//Get the challenge if one exists
			Challenge currentChallenge = this.race.getChallengeFromTellerID(columnIndex - 1);
			
			//If we got a challenge
			if(currentChallenge != null) {
				
				if(rowIndex == 0) {
					//If this is the first row

					//Show the bulletin board nonce
					byte[] bulletinBoardNonce = currentChallenge.bulletinBoardNonce;
					if(bulletinBoardNonce != null) {
						return encoder.encode(bulletinBoardNonce);
					} else {
						return null;
					}

				} else if(rowIndex == 1) {
					//If this is the second row

					//Show the commitment
					byte[] commitment = currentChallenge.commitment;
					if(commitment != null) {
						return encoder.encode(commitment);
					} else {
						return null;
					}

				} else if(rowIndex == 2) {
					//If this is the third row

					//Show the teller nonce
					byte[] tellerNonce = currentChallenge.tellerNonce;
					if(tellerNonce != null) {
						return encoder.encode(tellerNonce);
					} else {
						return null;
					}

				} else {
					//If this is the fourth row
					
					//Show the value
					byte[] value = currentChallenge.bitmap;
					if(value != null) {
						return encoder.encode(value);
					} else {
						return null;
					}
					
				}
				
			} else {
				return null;
			}
			
		}
	}
	
	public String getColumnName(int col) {
		if(col == 0) {
			return null;
		} else {
			return this.bulletinBoard.getTeller(col-1).name;
		}
	}

}
