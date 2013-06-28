package uk.ac.surrey.pav.administrator.treenodes;

import java.io.Serializable;
import java.security.PublicKey;
import java.util.Enumeration;

import javax.swing.tree.TreeNode;

import uk.ac.surrey.pav.administrator.EditableEntity;
import uk.ac.surrey.pav.common.HexConstructor;
import uk.ac.surrey.pav.common.interfaces.SQLable;

/**
 * Represents the teller
 * 
 * @author David Lundin
 *
 */
public class Teller implements TreeNode, SQLable, EditableEntity, Serializable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The parent TellerNode object
	 */
	private TellerNode parent;
	
	/**
	 * The name of the teller
	 */
	private String name;
	
	/**
	 * ID number of the teller
	 */
	private int id = -1;
	
	/**
	 * IP Address of the teller server
	 */
	private String ipAddress;
	
	/**
	 * Name of the server
	 */
	private String serverName;
	
	/**
	 * The public key of the teller
	 */
	private PublicKey publicKey;
	
	/**
	 * Returns the name of the teller
	 */
	public String getName() {
		return this.name;
	}

	/**
	 * Sets the name of the teller
	 */
	public void setName(String name) {
		this.name = name;
	}

	/**
	 * N/A
	 */
	public void removeNodeAt(int x) {
		//Not applicable
	}

	/**
	 * N/A
	 */
	public TreeNode getChildAt(int childIndex) {
		return null;
	}

	/**
	 * N/A
	 */
	public int getChildCount() {
		return 0;
	}

	/**
	 * Returns the parent TellerNode element
	 */
	public TreeNode getParent() {
		return this.parent;
	}

	/**
	 * N/A
	 */
	public int getIndex(TreeNode node) {
		return -1;
	}

	/**
	 * Does not have any children
	 */
	public boolean getAllowsChildren() {
		return false;
	}

	/**
	 * Is always a leaf
	 */
	public boolean isLeaf() {
		return true;
	}

	/**
	 * Doesn't have any children
	 */
	public Enumeration children() {
		return null;
	}
	
	/**
	 * Returns true if the teller has all the things it needs
	 * 
	 * @return True if the Teller is adequately set up to start
	 */
	public boolean isProper() {
		if(this.hasPublicKey() && this.name != "" && this.id >= 0 && this.ipAddress != "" && this.serverName != "") {
			return true;
		} else {
			return false;
		}
	}
	
	/**
	 * Constructor
	 * 
	 * @param parent
	 */
	public Teller(TellerNode parent) {
		this.parent = parent;
	}
	
	/**
	 * Sets the public key
	 */
	public void setPublicKey(PublicKey publicKey) {
		this.publicKey = publicKey;
	}
	
	/**
	 * A string representation of the object
	 */
	public String toString() {
		return this.name;
	}
	
	/**
	 * Returns true if there is a public key
	 */
	public boolean hasPublicKey() {
		if(this.publicKey != null) {
			return true;
		} else {
			return false;
		}
	}

	/**
	 * Sets the ID number
	 */
	public void setID(int id) {
		this.id = id;
	}

	/**
	 * Sets the IP Address of the server
	 */
	public void setIPAddress(String address) {
		this.ipAddress = address;
	}

	/**
	 * Sets the server name of the server
	 */
	public void setServerName(String serverName) {
		this.serverName = serverName;
	}

	/**
	 * Returns the ID number of this teller
	 */
	public int getID() {
		return this.id;
	}

	/**
	 * Returns the IP address of the teller server
	 */
	public String getIPAddress() {
		return this.ipAddress;
	}

	/**
	 * Returns the server name
	 */
	public String getServerName() {
		return this.serverName;
	}

	/**
	 * Returns a SQL INSERT statement for this teller
	 */
	public StringBuffer toSQL() {
		
		//The result variable
		StringBuffer result = new StringBuffer();
		
		result.append("INSERT INTO tellers (teller_id, teller_name, teller_ipaddress, teller_servername, teller_publickey, teller_sequencenumber) VALUES (");
		result.append(this.id + ", ");
		result.append("'" + this.name + "', ");
		result.append("'" + this.ipAddress + "', ");
		result.append("'" + this.serverName + "', ");
		result.append("x'" + HexConstructor.serializeIntoHex(this.publicKey) + "', ");
		result.append(((TellerNode)this.parent).getIndex(this));
		result.append(");");
		
		//Okay done, return
		return result;
		
	}
	
	/**
	 * Returns the public key of the teller
	 * 
	 * @return The PublicKey of the teller
	 */
	public PublicKey getPublicKey() {
		return this.publicKey;
	}

}
