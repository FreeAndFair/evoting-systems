package uk.ac.surrey.pav.misc;

import javax.swing.tree.TreeNode;

public interface SortableTreeNode extends TreeNode {
	
	public void removeNodeAt(int x);

	public void reorder();
	
}
