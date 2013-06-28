package uk.ac.surrey.pav.teller;

import java.security.PrivateKey;
import java.security.PublicKey;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.Iterator;

/**
 * Stores settings for the teller object
 * 
 * @author David Lundin
 *
 */
public class TellerSettings {

	/**
	 * The name of the teller itself, i.e. the organisation running it.
	 * Must correspond to the name held on the bulletin board because
	 * it is used when identifying to the bulletin board
	 */
	private String tellerName;
	
	/**
	 * Private key of the teller
	 */
	private PrivateKey privateKey;
	
	/**
	 * Public key of the bulletin board
	 */
	private PublicKey bulletinBoardPublicKey;
	
	/**
	 * Database connection string
	 */
	private String databaseConnectionString;
	
	/**
	 * The user name of the database
	 */
	private String databaseUserName;
	
	/**
	 * The password for the database
	 */
	private String databasePassword;
	
	/**
	 * Address to bind the teller server to
	 */
	private String serverAddress;
	
	/**
	 * Name to bind the teller server to
	 */
	private String serverName;
	
	/**
	 * Boolean describing whether or not the server is running
	 */
	private boolean statusBoolean = false;
	
	/**
	 * Human readable string representing the status of the server
	 */
	private String statusString = "Not running";
	
	/**
	 * A count of the number of ballot forms revealed 
	 */
	private int ballotAuditCount = 0;
	
	/**
	 * A cound of the number of batches processed
	 */
	private int batchProcessedCount = 0;
	
	/**
	 * A database connection
	 */
	public Connection databaseConnection;
	
	/**
	 * Those listening to the teller updated event
	 */
	private ArrayList tellerUpdatedListeners = new ArrayList();
	
	/**
	 * Server name of the bulletin board
	 */
	private String bulletinBoardServerName;
	
	/**
	 * Address of the bulletin board
	 */
	private String bulletinBoardServerAddress;

	/**
	 * Stores the new status of the server
	 * 
	 * @param newStatusBoolean The boolean that represents the current status of the teller
	 * @param newStatusString A string representing the current teller status in a human readable form
	 */
	public void setStatus(boolean newStatusBoolean, String newStatusString) {
		//Store the new status;
		this.statusBoolean = newStatusBoolean;
		this.statusString = newStatusString;
		
		//Fire an event to notify listeners
		this.fireTellerUpdatedEvent();

	}
	
	/**
	 * Returns true if the server is running
	 * 
	 * @return Boolean
	 */
	public boolean serverIsRunning() {
		return statusBoolean;
	}
	
	/**
	 * Returns the private key
	 * 
	 * @return PrivateKey
	 */
	public PrivateKey getPrivateKey() {
		return this.privateKey;
	}
	
	/**
	 * Returns the server name to bind to
	 * 
	 * @return String
	 */
	public String getServerName() {
		return this.serverName;
	}
	
	/**
	 * Increments the count of the number of ballot forms audited
	 *
	 */
	public void incrementBallotAuditCount() {
		this.ballotAuditCount++;
	}
	
	/**
	 * Increments the count of the number of batches processed
	 *
	 */
	public void incrementBatchProcessCount() {
		this.batchProcessedCount++;
	}
	
	/**
	 * Returns true if a teller server can be run on
	 * these settings
	 * 
	 * @return Boolean true if the settings are usable
	 */
	public boolean isProper() {
		
		if(this.serverAddress.length() > 0
				&& this.serverName.length() > 0
				&& this.privateKey != null
				&& this.databaseConnection != null) {
			return true;
		} else {
			return false;
		}
		
	}
	
	/**
	 * Sets a private key
	 * 
	 * @param newKey PrivateKey
	 */
	public void setPrivateKey(PrivateKey newKey) {
		this.privateKey = newKey;
		
		//Fire an event to notify listeners
		this.fireTellerUpdatedEvent();

	}
	
	/**
	 * Sets the public key of the bulletin board
	 * 
	 * @param newKey
	 */
	public void setPublicKey(PublicKey newKey) {
		this.bulletinBoardPublicKey = newKey;
		
		//Fire an event to notify listeners
		this.fireTellerUpdatedEvent();

	}
	
	/**
	 * Copy some settings
	 * 
	 * @param copySettings
	 */
	public void copySettings(TellerSettings copySettings) {
		this.tellerName = copySettings.tellerName;
		this.privateKey = copySettings.privateKey;
		this.serverAddress = copySettings.serverAddress;
		this.serverName = copySettings.serverName;
		this.bulletinBoardPublicKey = copySettings.bulletinBoardPublicKey;
		this.databaseConnectionString = copySettings.databaseConnectionString;
		this.databasePassword = copySettings.databasePassword;
		this.databaseUserName = copySettings.databaseUserName;
		this.bulletinBoardServerAddress = copySettings.bulletinBoardServerAddress;
		this.bulletinBoardServerName = copySettings.bulletinBoardServerName;
		
		//Fire an event to notify listeners
		this.fireTellerUpdatedEvent();

	}
	
	/**
	 * Returns the server address
	 * 
	 * @return String with the server address
	 */
	public String getServerAddress() {
		return this.serverAddress;
	}
	
	/**
	 * Set the server address
	 * 
	 * @param address
	 */
	public void setServerAddress(String address) {
		this.serverAddress = address;
		
		//Fire an event to notify listeners
		this.fireTellerUpdatedEvent();

	}
	
	/**
	 * Set the server name
	 * 
	 * @param name
	 */
	public void setServerName(String name) {
		this.serverName = name;
		
		//Fire an event to notify listeners
		this.fireTellerUpdatedEvent();

	}
	
	/**
	 * Returns the public key of the bulletin board
	 * 
	 * @return the public key of the bulletin board
	 */
	public PublicKey getBulletinBoardPublicKey() {
		return this.bulletinBoardPublicKey;
	}
	
	/**
	 * Returns the database connection string
	 * 
	 * @return The database connection string
	 */
	public String getDatabaseConnectionString() {
		return this.databaseConnectionString;
	}
	
	/**
	 * Returns the database user name
	 * 
	 * @return The database user name
	 */
	public String getDatabaseUserName() {
		return this.databaseUserName;
	}
	
	/**
	 * Returns the database password
	 * 
	 * @return The database password
	 */
	public String getDatabasePassword() {
		return this.databasePassword;
	}
	
	/**
	 * Connects to the database
	 * 
	 * @return True if the connection is successful
	 */
	public boolean connectToDatabase() {
	
		try {

			//Load the database connection driver
			Class.forName("com.mysql.jdbc.Driver");

			//Make the connection
			this.databaseConnection = DriverManager.getConnection(this.databaseConnectionString, this.databaseUserName, this.databasePassword);
			
			//We are connected, return true
			return true;
			
		} catch (ClassNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			return false;
		} catch (SQLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			return false;
		}


	}
	
	/**
	 * Sets the database connection string
	 * @param connectionString
	 */
	public void setDatabaseConnectionString(String connectionString) {
		this.databaseConnectionString = connectionString;
		
		//Fire an event to notify listeners
		this.fireTellerUpdatedEvent();
	}
	
	/**
	 * Sets the database password
	 * 
	 * @param password
	 */
	public void setDatabasePassword(String password) {
		this.databasePassword = password;

		//Fire an event to notify listeners
		this.fireTellerUpdatedEvent();
	}
	
	/**
	 * Sets the database user name
	 * 
	 * @param userName
	 */
	public void setDatabaseUserName(String userName) {
		this.databaseUserName = userName;

		//Fire an event to notify listeners
		this.fireTellerUpdatedEvent();
	}
	
	public String getStatusString() {
		return this.statusString;
	}
	
	public int getBallotAuditCount() {
		return this.ballotAuditCount;
	}
	
	public int getBatchProcessedCount() {
		return this.batchProcessedCount;
	}
	
	/**
	 * Adds a listener for the teller updated event
	 * 
	 * @param listener
	 */
	public void addTellerUpdatedListener(TellerUpdatedListener listener) {
		this.tellerUpdatedListeners.add(listener);
	}
	
	/**
	 * Sends the teller updated event to all listeners
	 *
	 */
	private void fireTellerUpdatedEvent() {
		
		//All the listeners
		Iterator listeners = this.tellerUpdatedListeners.iterator();
		
		//System.out.println("There are " + this.tellerUpdatedListeners.size() + " listeners for the teller updated event.");
		
		//Fire on each listener
		while(listeners.hasNext()) {
			((TellerUpdatedListener)listeners.next()).receiveTellerUpdatedEvent(new TellerUpdatedEvent(this));
		}

	}

	public String getBulletinBoardServerAddress() {
		return bulletinBoardServerAddress;
	}

	public void setBulletinBoardServerAddress(String bulletinBoardServerAddress) {
		this.bulletinBoardServerAddress = bulletinBoardServerAddress;
	}

	public String getBulletinBoardServerName() {
		return bulletinBoardServerName;
	}

	public void setBulletinBoardServerName(String bulletinBoardServerName) {
		this.bulletinBoardServerName = bulletinBoardServerName;
	}

	public String getTellerName() {
		return tellerName;
	}

	public void setTellerName(String tellerName) {
		this.tellerName = tellerName;
	}
	
}
