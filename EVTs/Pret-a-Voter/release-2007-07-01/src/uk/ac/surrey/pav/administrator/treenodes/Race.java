package uk.ac.surrey.pav.administrator.treenodes;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Enumeration;
import java.util.Iterator;

import javax.swing.tree.TreeNode;

import uk.ac.surrey.pav.administrator.NameEditableEntity;
import uk.ac.surrey.pav.common.interfaces.SQLable;

/**
 * Holds information about a race in a particular election that
 * is being set up by the Administrator module.
 * 
 * @author David Lundin
 *
 */
public class Race implements NameEditableEntity, ChildRemovableTreeNode, Comparable, SQLable, Serializable {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The name of this race
	 */
	public String name;
	
	/**
	 * The candidates in this race
	 */
	public ArrayList candidates = new ArrayList();
	
	/**
	 * Parent node
	 */
	public TreeNode parent;
	
	/**
	 * Returns the name of the race
	 */
	public String toString() {
		return this.name;
	}
	
	/**
	 * Adds a new candidate to this race
	 * Candidates are sorted, the order is determined by
	 * <code>name.compareTo(anotherCandidate.toString())</code>
	 * 
	 * @param c The candidate to be added
	 */
	public void addCandidate(Candidate c) {
		candidates.add(c);
		reorder();
	}
	
	/**
	 * Default constructor
	 * 
	 * @param name	Name of the race
	 */
	public Race(String name, TreeNode parent) {
		this.name = name;
		this.parent = parent;
	}

	/**
	 * Returns the child nodes
	 */
	public Enumeration children() {
		return Collections.enumeration(candidates);
	}
	
	/**
	 * Returns the number of child nodes
	 */
	public int getChildCount() {
		return candidates.size();
	}
	
	/**
	 * Returns true if this is a leaf node
	 */
	public boolean isLeaf() {
		if(candidates.size() == 0) return true;
		else return false;
	}
	
	/**
	 * Returns the parent element
	 */
	public TreeNode getParent() {
		return this.parent;
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
		return (TreeNode)candidates.get(childIndex);
	}
	
	/**
	 * Returns the index of specified child node
	 */
	public int getIndex(TreeNode node) {
		for(int x = 0; x < candidates.size(); x++) {
			if(candidates.get(x) == node) return x;
		}
		return -1;
	}
	
	/**
	 * Returns true if the name of a given candidate is duplicated
	 * 
	 * @param c The candidate to be tested
	 */
	public boolean hasDuplicatedCandidate(Candidate c) {
		for(Iterator i = candidates.iterator(); i.hasNext();){
			if(i.next().toString().equalsIgnoreCase(c.toString()))
				return true;
		}
		return false;
	}

	public int compareTo(Object o) {
		return this.name.compareTo(((Race)o).toString());
	}

	public String getName() {
		return this.toString();
	}

	public void setName(String name) {
		this.name = name;
		reorder();
	}
	
	public void reorder() {
		Collections.sort(candidates);
	}

	public void removeNodeAt(int x) {
		candidates.remove(x);
	}
	
	/**
	 * Returns a SQL INSERT statement for this race
	 */
	public StringBuffer toSQL() {
		
		//The result variable
		StringBuffer result = new StringBuffer();
		
		result.append("INSERT INTO races (election_id, race_id, race_name) VALUES (");
		result.append(((Election)this.parent).parent.getIndex((Election)this.parent) + ", ");
		result.append(((Election)this.parent).getIndex(this) + ", ");
		result.append("'" + this.name + "'");
		result.append(");");
		
		//Okay done, return
		return result;
		
	}
	
	/**
	 * Returns the number of candidates in this race
	 * 
	 * @return The number of candidates
	 */
	public int getNumberOfCandidates() {
		
		return this.candidates.size();
		
	}

	/**
	 * Removes a particular candidate
	 */
	public void removeChild(Object child) {
		this.candidates.remove(child);
	}

}
