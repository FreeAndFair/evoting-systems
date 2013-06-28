package uk.ac.surrey.pav.administrator.treenodes;

import java.io.Serializable;
import java.security.PublicKey;
import java.util.ArrayList;
import java.util.Enumeration;

import javax.swing.tree.TreeNode;

import uk.ac.surrey.pav.administrator.EditableEntity;
import uk.ac.surrey.pav.common.HexConstructor;
import uk.ac.surrey.pav.common.interfaces.SQLable;

/**
 * Holds information about the voting booth
 * 
 * @author David Lundin
 *
 */
public class Booth implements TreeNode, SQLable, EditableEntity, Serializable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The parent BoothNode element
	 */
	private BoothNode parent;
	
	/**
	 * A list of booths
	 */
	private ArrayList booths = new ArrayList();
	
	/**
	 * The name of the booth
	 */
	private String name;
	
	/**
	 * The public key of the booth
	 */
	private PublicKey publicKey;
	
	/**
	 * The booth ID
	 */
	private int id = -1;
	
	/**
	 * Returns the name of the booth
	 */
	public String getName() {
		return this.name;
	}

	/**
	 * Sets the name
	 */
	public void setName(String name) {
		this.name = name;
	}

	/**
	 * Remove a particular booth from the list
	 */
	public void removeNodeAt(int x) {
		this.booths.remove(x);
	}

	/**
	 * Get the booth in a particular place in the list
	 */
	public TreeNode getChildAt(int childIndex) {
		return (Booth)this.booths.get(childIndex);
	}

	/**
	 * Return the number of booths
	 */
	public int getChildCount() {
		return this.booths.size();
	}

	/**
	 * Returns the parent RootNode element
	 */
	public TreeNode getParent() {
		return this.parent;
	}

	/**
	 * Returns the index of a particular booth in the list
	 */
	public int getIndex(TreeNode node) {
		for (int x = 0; x < this.booths.size(); x++) {
			if (this.booths.get(x) == node)
				return x;
		}
		return -1;
	}

	/**
	 * This cannot have children
	 */
	public boolean getAllowsChildren() {
		return false;
	}

	/**
	 * This is always a leaf
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
	 * Constructor
	 * 
	 * @param parent
	 */
	public Booth(BoothNode parent) {
		this.parent = parent;
	}

	/**
	 * Sets the public key
	 */
	public void setPublicKey(PublicKey publicKey) {
		this.publicKey = publicKey;
	}

	/**
	 * Check if there is a public key
	 */
	public boolean hasPublicKey() {
		if(this.publicKey != null) {
			return true;
		} else {
			return false;
		}
	}

	/**
	 * Returns true if the object has all the elements needed
	 */
	public boolean isProper() {
		if(this.hasPublicKey() && this.id >= 0 && this.name != "") {
			return true;
		} else {
			return false;
		}
	}

	/**
	 * Set the ID
	 */
	public void setID(int id) {
		this.id = id;
	}

	/**
	 * Return the ID
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
	 * String representation of the booth node
	 */
	public String toString() {
		return this.name;
	}

	/**
	 * Returns a SQL INSERT statement for this booth
	 */
	public StringBuffer toSQL() {
		
		//The result variable
		StringBuffer result = new StringBuffer();
		
		result.append("INSERT INTO booths (booth_id, booth_name, booth_publickey) VALUES (");
		result.append(this.id + ", ");
		result.append("'" + this.name + "', ");
		result.append("x'" + HexConstructor.serializeIntoHex(this.publicKey) + "'");
		result.append(");");
		
		//Okay done, return
		return result;
		
	}

}
