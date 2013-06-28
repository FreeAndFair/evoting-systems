package uk.ac.surrey.pav.administrator.treenodes;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Enumeration;

import javax.swing.tree.TreeNode;

/**
 * Keeps track of all the voting booths in the list and displays these in the GUI JTree
 * 
 * @author David Lundin
 *
 */
public class BoothNode implements ChildRemovableTreeNode, Serializable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The parent Root object
	 */
	private TreeNode parent;
	
	/**
	 * The list of booths
	 */
	private ArrayList booths = new ArrayList();
	
	/**
	 * The booth at a particular position
	 */
	public TreeNode getChildAt(int childIndex) {
		return (Booth)this.booths.get(childIndex);
	}

	/**
	 * The number of booths in the list
	 */
	public int getChildCount() {
		return this.booths.size();
	}

	/**
	 * Returns the parent Root node
	 */
	public TreeNode getParent() {
		return this.parent;
	}

	/**
	 * Returns the index of a particular booth
	 */
	public int getIndex(TreeNode node) {
		for (int x = 0; x < this.booths.size(); x++) {
			if (this.booths.get(x) == node)
				return x;
		}
		return -1;
	}

	/**
	 * This node can have children
	 */
	public boolean getAllowsChildren() {
		return true;
	}

	/**
	 * This is not a leaf if there are any booths in the list
	 */
	public boolean isLeaf() {
		if(this.booths.size() > 0) {
			return false;
		} else {
			return true;
		}
	}

	/**
	 * All the children
	 */
	public Enumeration children() {
		return Collections.enumeration(this.booths);
	}

	/**
	 * Constructor
	 * @param parent
	 */
	public BoothNode(Root parent) {
		this.parent = parent;
	}
	
	/**
	 * String representation of the node
	 */
	public String toString() {
		return "Voting booths";
	}
	
	/**
	 * Add a booth to the list
	 * 
	 * @param booth
	 */
	public void addBooth(Booth booth) {
		this.booths.add(booth);
	}

	/**
	 * Removes a particular child
	 */
	public void removeChild(Object child) {
		this.booths.remove(child);
	}

}
