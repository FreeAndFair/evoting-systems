package uk.ac.surrey.pav.misc;

import java.net.MalformedURLException;
import java.rmi.Naming;
import java.rmi.NotBoundException;
import java.rmi.RemoteException;

import uk.ac.surrey.pav.bulletinboard.BulletinBoard;
import uk.ac.surrey.pav.bulletinboard.BulletinBoardServer;

/**
 * Thread that runs the bulletin board server
 * 
 * @author David Lundin
 *
 */
public class BulletinBoardThread extends Thread {

	/**
	 * A reference to the bulletin board server that is set up
	 */
	private BulletinBoardServer bulletinBoardServer;
	
	/**
	 * Whether or not to keep the server online
	 */
	private boolean keepRunning = true;
		
	/**
	 * Constructor that sets up a new server
	 * 
	 * @param bulletinBoard The bulletin board object that holds information about the election to be run
	 */
	public BulletinBoardThread(BulletinBoard bulletinBoard) {
		try {
			//Start new server and store reference
			this.bulletinBoardServer = new BulletinBoardServer(bulletinBoard);
		} catch (RemoteException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	/**
	 * Runs the server
	 */
	public void run() {
		//As long as the server is to run keep rebinding every second
		while(this.keepRunning) {
			//Sleep for one second
			try {
				Naming.rebind("Bulletinboard", this.bulletinBoardServer);
				this.sleep(1000);
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (MalformedURLException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (RemoteException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		
		//Now safe to turn the server off
		try {
			Naming.unbind("WBB");
		} catch (RemoteException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (MalformedURLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (NotBoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
}
