package uk.ac.surrey.pav.teller;

import javax.swing.table.AbstractTableModel;

/**
 * Displays a list of settings for the teller
 * 
 * @author David Lundin
 *
 */
public class TellerTableModel extends AbstractTableModel implements TellerUpdatedListener {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	/**
	 * The settings to set out
	 */
	TellerSettings settings;
	
	/**
	 * The names of the variables that are set out
	 */
	private String[] variableNames = {
			"Teller Name",
			"Server Address",
			"Server Name",
			"Private Key",
			"Ballot forms audited",
			"Batches processed",
			"Bulletin board address",
			"Bulletin board server name",
			"Bulletin board public key",
			"Database connection",
			"Database connection string",
			"Database user name",
			"Database password",
			"Server status"
	};
	
	/**
	 * There are two columns in this table
	 */
	public int getColumnCount() {
		return 2;
	}

	/**
	 * There are six rows
	 */
	public int getRowCount() {
		return 14;
	}

	/**
	 * Returns the value in a particular cell
	 */
	public Object getValueAt(int rowIndex, int columnIndex) {
		if(columnIndex == 0) {
			return this.variableNames[rowIndex];
		} else {
			switch(rowIndex) {

			case 0:
				return this.settings.getTellerName();
			case 1:
				return this.settings.getServerAddress();
			case 2:
				return this.settings.getServerName();
			case 3:
				if(this.settings.getPrivateKey() != null) {
					return this.settings.getPrivateKey().toString();
				} else {
					return "(not loaded)";
				}
			case 4:
				return this.settings.getBallotAuditCount() + "";
			case 5:
				return this.settings.getBatchProcessedCount() + "";
			case 6:
				return this.settings.getBulletinBoardServerAddress();
			case 7:
				return this.settings.getBulletinBoardServerName();
			case 8:
				if(this.settings.getBulletinBoardPublicKey() != null) {
					return this.settings.getBulletinBoardPublicKey();
				} else {
					return "(not loaded)";
				}
			case 9:
				if(this.settings.databaseConnection != null) {
					return "Connected";
				} else {
					return "Not connected";
				}
			case 10:
				return this.settings.getDatabaseConnectionString();
			case 11:
				return this.settings.getDatabaseUserName();
			case 12:
				return "*******";
			default:
				return this.settings.getStatusString();
			}
		}
	}

	/**
	 * Returns the name of a column
	 */
	public String getColumnName(int col) {
		if(col == 0) {
			return "Variable";
		} else {
			return "Value";
		}
	}
	
	/**
	 * Constructor
	 * 
	 * @param settings
	 */
	public TellerTableModel(TellerSettings settings) {
		//Store reference to the settings
		this.settings = settings;
		
		//Register as a listener
		this.settings.addTellerUpdatedListener(this);
	}

	/**
	 * Receive the teller updated event
	 */
	public void receiveTellerUpdatedEvent(TellerUpdatedEvent event) {
		this.fireTableDataChanged();
	}

}
