package uk.ac.surrey.pav.audit;

/**
 * Stores settings for the database auditor
 * 
 * @author David Lundin
 *
 */
public class AuditorSettings {

	private String databaseConnectionString;
	
	private String databaseUserName;
	
	private String databasePassword;

	public String getDatabaseConnectionString() {
		return databaseConnectionString;
	}

	public void setDatabaseConnectionString(String databaseConnectionString) {
		this.databaseConnectionString = databaseConnectionString;
	}

	public String getDatabasePassword() {
		return databasePassword;
	}

	public void setDatabasePassword(String databasePassword) {
		this.databasePassword = databasePassword;
	}

	public String getDatabaseUserName() {
		return databaseUserName;
	}

	public void setDatabaseUserName(String databaseUserName) {
		this.databaseUserName = databaseUserName;
	}
	
}
