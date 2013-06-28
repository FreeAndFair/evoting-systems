package uk.ac.surrey.pav.administrator;

import java.security.PublicKey;

/**
 * An entity that is editable
 * 
 * @author David Lundin
 *
 */
public interface EditableEntity {

	public void setName(String name);

	public void setPublicKey(PublicKey publicKey);
	
	public String getName();
	
	public boolean hasPublicKey();
	
	public boolean isProper();
	
	public void setID(int id);
	
	public int getID();
	
	public void setIPAddress(String address);
	
	public String getIPAddress();
	
	public void setServerName(String serverName);
	
	public String getServerName();
	
}
