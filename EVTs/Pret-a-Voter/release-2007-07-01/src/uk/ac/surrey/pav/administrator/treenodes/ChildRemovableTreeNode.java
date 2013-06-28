package uk.ac.surrey.pav.administrator.treenodes;

import javax.swing.tree.TreeNode;

/**
 * A tree node that can have its child removed
 * 
 * @author David Lundin
 *
 */
public interface ChildRemovableTreeNode extends TreeNode {

	public void removeChild(Object child);
	
}
