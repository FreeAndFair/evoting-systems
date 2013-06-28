package uk.ac.surrey.pav.common;

import java.net.MalformedURLException;
import java.rmi.Naming;
import java.rmi.NotBoundException;
import java.rmi.RemoteException;
import java.security.PrivateKey;

import uk.ac.surrey.pav.bulletinboard.BulletinBoardInterface;

/**
 * Stores the settings for clients that connect to the bulletin board
 * 
 * @author David Lundin
 *
 */
public class ClientSettings {

	/**
	 * My ID
	 */
	public int ID;

	/**
	 * My private key
	 */
	public PrivateKey privateKey;
	
	/**
	 * URL of the bulletin board
	 */
	public String bulletinBoardAddress;
	
	/**
	 * The RMI server name of the bulletin board
	 */
	public String bulletinBoardName;
	
	/**
	 * An RMI connection to the bulletin board server
	 */
	public BulletinBoardInterface bulletinBoardServer;
	
	/**
	 * Default constructor
	 *
	 */
	public ClientSettings() {
		
	}
	
	/**
	 * Copies the settings from a supplied settings object to this
	 * 
	 * @param newSettings AuditMachineSettings with settings to copy to this
	 */
	public void copySettings(ClientSettings newSettings) {
		this.ID = newSettings.ID;
		this.privateKey = newSettings.privateKey;
		this.bulletinBoardAddress = newSettings.bulletinBoardAddress;
		this.bulletinBoardName = newSettings.bulletinBoardName;
	}
	
	/**
	 * Returns true if this contains proper settings
	 * 
	 * @return boolean
	 */
	public boolean isProperSettings() {

		if(this.privateKey != null && this.bulletinBoardAddress != "" && this.bulletinBoardName != null) {
			return true;
		} else {
			return false;
		}

	}
	
	/**
	 * Connect to the bulletin board
	 *
	 */
	public void connectToBulletinBoardServer() {
		
		try {
			
			//Connect to the web bulletin board
			this.bulletinBoardServer = (BulletinBoardInterface)Naming.lookup("rmi://" + this.bulletinBoardAddress + "/" + this.bulletinBoardName);
			
		} catch (MalformedURLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (RemoteException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (NotBoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

	}
	
	/**
	 * Returns true if we are connected
	 * 
	 * @return True if connected
	 */
	public boolean isConnected() {
		
		if(this.bulletinBoardServer != null) {
			return true;
		} else {
			return false;
		}
		
	}
	
}
