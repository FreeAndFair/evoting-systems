package uk.ac.surrey.pav.administrator.treenodes;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Enumeration;

import javax.swing.tree.TreeNode;

/**
 * Keeps a list of audit machines and sets this out in the GUI JTree
 * 
 * @author David Lundin
 *
 */
public class AuditMachineNode implements ChildRemovableTreeNode, Serializable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The parent Root element
	 */
	private TreeNode parent;
	
	/**
	 * The list of audit machines
	 */
	private ArrayList auditMachines = new ArrayList();
	
	/**
	 * Returns a particular audit machine from the list
	 */
	public TreeNode getChildAt(int childIndex) {
		return (AuditMachine)this.auditMachines.get(childIndex);
	}

	/**
	 * Returns the number of audit machines in the list
	 */
	public int getChildCount() {
		return this.auditMachines.size();
	}

	/**
	 * Returns the parent Root object
	 */
	public TreeNode getParent() {
		return this.parent;
	}

	/**
	 * Returns the index of a particular audit machine in the list
	 */
	public int getIndex(TreeNode node) {
		for (int x = 0; x < this.auditMachines.size(); x++) {
			if (this.auditMachines.get(x) == node)
				return x;
		}
		return -1;
	}

	/**
	 * This does have children
	 */
	public boolean getAllowsChildren() {
		return true;
	}

	/**
	 * This is a leaf if there are no audit machines in the list
	 */
	public boolean isLeaf() {
		if(this.auditMachines.size() > 0) {
			return false;
		} else {
			return true;
		}
	}

	/**
	 * Returns an enumeration of all the audit machines
	 */
	public Enumeration children() {
		return Collections.enumeration(this.auditMachines);
	}
	
	/**
	 * Constructor
	 * 
	 * @param parent
	 */
	public AuditMachineNode(Root parent) {
		this.parent = parent;
	}
	
	/**
	 * String representation of the node
	 */
	public String toString() {
		return "Audit machines";
	}
	
	/**
	 * Adds an audit machine to the list
	 * 
	 * @param auditMachine
	 */
	public void addAuditMachine(AuditMachine auditMachine) {
		this.auditMachines.add(auditMachine);
	}

	/**
	 * Removes a particular child
	 */
	public void removeChild(Object child) {
		this.auditMachines.remove(child);
	}

}
