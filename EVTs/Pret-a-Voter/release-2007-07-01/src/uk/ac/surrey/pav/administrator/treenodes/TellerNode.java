package uk.ac.surrey.pav.administrator.treenodes;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Enumeration;

import javax.swing.tree.TreeNode;

/**
 * Keeps track of the tellers created and also sets this section of the
 * tree out in the GUI.
 * 
 * @author David Lundin
 *
 */
public class TellerNode implements ChildRemovableTreeNode, Serializable {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The tellers
	 */
	private ArrayList tellers = new ArrayList();

	/**
	 * The parent Root element
	 */
	private Root parent;
	
	/**
	 * Returns a particular teller
	 */
	public TreeNode getChildAt(int childIndex) {
		return (Teller)this.tellers.get(childIndex);
	}

	/**
	 * Returns the number of tellers in the list
	 */
	public int getChildCount() {
		return this.tellers.size();
	}

	/**
	 * Returns the parent Root element
	 */
	public TreeNode getParent() {
		return parent;
	}

	/**
	 * Returns the index of a particular teller
	 */
	public int getIndex(TreeNode node) {
		for (int x = 0; x < this.tellers.size(); x++) {
			if (this.tellers.get(x) == node)
				return x;
		}
		return -1;
	}

	/**
	 * Returns true because this node allows children
	 */
	public boolean getAllowsChildren() {
		return true;
	}

	/**
	 * This node is not a leaf
	 */
	public boolean isLeaf() {
		if(this.tellers.size() > 0) {
			return false;
		} else {
			return true;
		}
	}

	/**
	 * Returns an Enumeration fo all the tellers
	 */
	public Enumeration children() {
		return Collections.enumeration(this.tellers);
	}
	
	/**
	 * Constructor
	 * 
	 * @param parent
	 */
	public TellerNode(Root parent) {
		this.parent = parent;
	}
	
	/**
	 * Returns string representation of the node
	 */
	public String toString() {
		return "Tellers";
	}
	
	/**
	 * Add a new teller to the list
	 * 
	 * @param teller
	 */
	public void addTeller(Teller teller) {
		this.tellers.add(teller);
	}

	/**
	 * Removes a particular child
	 */
	public void removeChild(Object child) {
		this.tellers.remove(child);
	}

}
