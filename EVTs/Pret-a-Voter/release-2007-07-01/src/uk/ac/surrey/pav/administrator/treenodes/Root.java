package uk.ac.surrey.pav.administrator.treenodes;

import java.io.Serializable;
import java.util.Enumeration;
import java.util.Vector;

import javax.swing.tree.TreeNode;


/**
 * Is used to set up an election, print ballot forms and so forth.
 * 
 * @author David Lundin, Joson Xia
 * 
 */
public class Root implements TreeNode, Serializable {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	private String name = "Administrator";

	/**
	 * A teller node, holding a number of tellers
	 */
	private TellerNode tellerNode;
	
	/**
	 * The elections
	 */
	private ElectionNode electionNode;
	
	/**
	 * The booths
	 */
	private BoothNode boothNode;
	
	/**
	 * The audit machines
	 */
	private AuditMachineNode auditMachineNode;

	public Root() {
		
		//Create a teller node
		this.tellerNode = new TellerNode(this);
		
		//Create a booth node
		this.boothNode = new BoothNode(this);
		
		//Create an audit machine node
		this.auditMachineNode = new AuditMachineNode(this);
		
		//Create an election node
		this.electionNode = new ElectionNode(this);
		
	}
	
	/**
	 * Returns string representation of the root node
	 */
	public String toString() {
		return this.name;
	}

	/**
	 * Returns the child nodes
	 */
	public Enumeration children() {
		Vector result = new Vector();
		result.add(this.tellerNode);
		result.add(this.boothNode);
		result.add(this.auditMachineNode);
		result.add(this.electionNode);
		return result.elements();
	}

	/**
	 * Returns the number of child nodes
	 */
	public int getChildCount() {
		return 4;
	}

	/**
	 * Returns true if this is a leaf node
	 */
	public boolean isLeaf() {
		return false;
	}

	/**
	 * Returns the parent element
	 */
	public TreeNode getParent() {
		return null;
	}

	/**
	 * Returns true because child nodes are allowed
	 */
	public boolean getAllowsChildren() {
		return true;
	}

	/**
	 * Returns child node with index childIndex
	 */
	public TreeNode getChildAt(int childIndex) {
		if(childIndex == 0) {
			return this.tellerNode;
		} else if(childIndex == 1) {
			return this.boothNode;
		} else if(childIndex == 2) {
			return this.auditMachineNode;
		} else {
			return this.electionNode;
		}
	}

	/**
	 * Returns the index of specified child node
	 */
	public int getIndex(TreeNode node) {
		if(node == this.electionNode) {
			return 3;
		} else if(node == this.boothNode) {
			return 1;
		} else if(node == this.auditMachineNode) {
			return 2;
		} else {
			return 0;
		}
	}

}
