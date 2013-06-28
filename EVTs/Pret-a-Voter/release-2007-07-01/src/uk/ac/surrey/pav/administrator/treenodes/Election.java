package uk.ac.surrey.pav.administrator.treenodes;

import java.io.Serializable;
import java.sql.Date;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Enumeration;
import java.util.Iterator;

import javax.swing.tree.TreeNode;

import uk.ac.surrey.pav.administrator.NameEditableEntity;
import uk.ac.surrey.pav.common.interfaces.SQLable;

/**
 * Holds information about an election that is being set up by the Administrator
 * module.
 * 
 * @author David Lundin
 * 
 */
public class Election implements NameEditableEntity, ChildRemovableTreeNode, SQLable, Serializable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * Name of the election
	 */
	private String name;

	/**
	 * The races in this election
	 */
	private ArrayList races = new ArrayList();

	/**
	 * Parent node
	 */
	public ElectionNode parent;
	
	/**
	 * Election start date
	 */
	private Date startDate;
	
	/**
	 * Election end date
	 */
	private Date endDate;

	/**
	 * Returns the name of the election
	 */
	public String toString() {
		
		return this.name + " (" + this.startDate.toString() + " to " + this.endDate.toString() + ")";
		
	}

	/**
	 * Adds a race to the election
	 * Races are sorted, the order is determined by
	 * <code>name.compareTo(anotherRace.toString())</code>
	 * @param r The race to be added
	 */
	public void addRace(Race r) {
		this.races.add(r);
		//reorder();
	}

	/**
	 * Default constructor for the election
	 * 
	 * @param parent The tree node under which this election is set on screen
	 */
	public Election(ElectionNode parent) {
		this.parent = parent;
	}

	/**
	 * Returns the child nodes
	 */
	public Enumeration children() {
		return Collections.enumeration(races);
	}

	/**
	 * Returns the number of child nodes
	 */
	public int getChildCount() {
		return races.size();
	}

	/**
	 * Returns true if this is a leaf node
	 */
	public boolean isLeaf() {
		if (races.size() == 0)
			return true;
		else
			return false;
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
		return (TreeNode) races.get(childIndex);
	}

	/**
	 * Returns the index of specified child node
	 */
	public int getIndex(TreeNode node) {
		for (int x = 0; x < races.size(); x++) {
			if (races.get(x) == node)
				return x;
		}
		return -1;
	}
	
	/**
	 * Returns true if the name of a given race is duplicated
	 * 
	 * @param r The race to be tested
	 */
	public boolean hasDuplicatedRace(Race r) {
		for(Iterator i = races.iterator(); i.hasNext();){
			if(i.next().toString().equalsIgnoreCase(r.toString()))
				return true;
		}
		return false;
	}

	public String getName() {
		return this.name;
	}

	public void setName(String name) {
		this.name = name;
	}
	public void reorder() {
		Collections.sort(races);
	}

	public void removeNodeAt(int x) {
		races.remove(x);
	}

	/**
	 * Returns a SQL INSERT statement for this election
	 */
	public StringBuffer toSQL() {
		
		//The result variable
		StringBuffer result = new StringBuffer();
		
		result.append("INSERT INTO elections (election_id, election_name, election_startdate, election_enddate) VALUES (");
		result.append(this.parent.getIndex(this) + ", ");
		result.append("'" + this.name + "', ");
		result.append("'" + this.startDate.toString() + "', ");
		result.append("'" + this.endDate.toString() + "'");
		result.append(");");
		
		//Okay done, return
		return result;
		
	}
	
	/**
	 * Returns the number of candidates in all races in this election
	 * 
	 * @return The number of candidates in the election
	 */
	public int getNumberOfCandidates (){
		
		//What we are returning
		int result = 0;
		
		//For each race
		for(int x=0; x < this.races.size(); x++) {
			result += ((Race)this.races.get(x)).getNumberOfCandidates();
		}
		
		//Done, return
		return result;
		
	}

	/**
	 * Removes a particular race
	 */
	public void removeChild(Object child) {
		this.races.remove(child);
	}
	
	public Date getStartDate() {
		return this.startDate;
	}
	
	public Date getEndDate() {
		return this.endDate;
	}
	
	public void setStartDate(Date startDate) {
		this.startDate = startDate;
	}
	
	public void setEndDate(Date endDate) {
		this.endDate = endDate;
	}
	
	/**
	 * Returns true if the election has all the proper details set up
	 */
	public boolean isProper() {
		
		if(this.name.length() > 0
				&& this.startDate != null
				&& this.endDate != null) {
			
			return true;
			
		} else {
			
			return false;
			
		}
				
	}

}
