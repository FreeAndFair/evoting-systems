package uk.ac.surrey.pav.administrator.treenodes;

import java.io.Serializable;
import java.security.PublicKey;
import java.util.Enumeration;

import javax.swing.tree.TreeNode;

import uk.ac.surrey.pav.administrator.EditableEntity;
import uk.ac.surrey.pav.common.HexConstructor;
import uk.ac.surrey.pav.common.interfaces.SQLable;

/**
 * Holds information about an audit machine and sets it out in the GUI JTree
 * 
 * @author David Lundin
 *
 */
public class AuditMachine implements TreeNode, SQLable, EditableEntity, Serializable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The name of the audit machine
	 */
	private String name;
	
	/**
	 * The parent AuditMachineNode element
	 */
	private AuditMachineNode parent;
	
	/**
	 * Public key of the audit machine
	 */
	private PublicKey publicKey;
	
	/**
	 * Audit machine ID
	 */
	private int id = -1;
	
	/**
	 * Returns the name of the audit machine
	 */
	public String getName() {
		return this.name;
	}

	/**
	 * Sets the name of the audit machine
	 */
	public void setName(String name) {
		this.name = name;
	}

	/**
	 * N/A
	 */
	public void removeNodeAt(int x) {
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
	 * Returns the parent AuditMachineNode element
	 */
	public TreeNode getParent() {
		return this.parent;
	}

	/**
	 * N/A
	 */
	public int getIndex(TreeNode node) {
		return 0;
	}

	/**
	 * Does not have children
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
	 * N/A
	 */
	public Enumeration children() {
		return null;
	}

	/**
	 * Sets the public key
	 */
	public void setPublicKey(PublicKey publicKey) {
		this.publicKey = publicKey;
	}

	/**
	 * Checks if there is a public key
	 */
	public boolean hasPublicKey() {
		if(this.publicKey != null) {
			return true;
		} else {
			return false;
		}
	}

	/**
	 * Checks if all information needed has been entered
	 */
	public boolean isProper() {
		if(this.hasPublicKey() && this.id >= 0 && this.name != "") {
			return true;
		} else {
			return false;
		}
	}

	/**
	 * Sets the ID
	 */
	public void setID(int id) {
		this.id = id;
	}

	/**
	 * Returns the ID
	 */
	public int getID() {
		return this.id;
	}

	/**
	 * N/A
	 */
	public void setIPAddress(String address) {
	}

	/**
	 * N/A
	 */
	public String getIPAddress() {
		return null;
	}

	/**
	 * N/A
	 */
	public void setServerName(String serverName) {
	}

	/**
	 * N/A
	 */
	public String getServerName() {
		return null;
	}

	/**
	 * String representation of the node
	 */
	public String toString() {
		return this.name;
	}
	
	/**
	 * Constructor
	 * 
	 * @param parent
	 */
	public AuditMachine(AuditMachineNode parent) {
		this.parent = parent;
	}

	/**
	 * Returns a SQL INSERT statement for this audit machine
	 */
	public StringBuffer toSQL() {
		
		//The result variable
		StringBuffer result = new StringBuffer();
		
		result.append("INSERT INTO auditmachines (auditmachine_id, auditmachine_name, auditmachine_publickey) VALUES (");
		result.append(this.id + ", ");
		result.append("'" + this.name + "', ");
		result.append("x'" + HexConstructor.serializeIntoHex(this.publicKey) + "'");
		result.append(");");
		
		//Okay done, return
		return result;
		
	}

}
