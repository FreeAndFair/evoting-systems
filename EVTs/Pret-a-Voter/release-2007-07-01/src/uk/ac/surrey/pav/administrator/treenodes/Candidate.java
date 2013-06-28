package uk.ac.surrey.pav.administrator.treenodes;

import java.io.Serializable;
import java.util.Enumeration;

import javax.swing.tree.TreeNode;

import uk.ac.surrey.pav.administrator.NameEditableEntity;
import uk.ac.surrey.pav.common.interfaces.SQLable;


/**
 * A candidate in a race in an election being set
 * up by the Administrator module.
 * 
 * @author David Lundin
 *
 */
public class Candidate implements NameEditableEntity, TreeNode, Comparable, SQLable, Serializable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The name of the candidate
	 */
	public String name;
	
	/**
	 * Parent node
	 */
	private Race parent;
	
	/**
	 * Returns the name of the candidate
	 */
	public String toString() {
		return this.name;
	}
	
	/**
	 * Default constructor
	 * 
	 * @param name	Name of the candidate
	 */
	public Candidate(String name, Race parent) {
		this.name = name;
		this.parent = parent;
	}

	/**
	 * Returns the child nodes
	 */
	public Enumeration children() {
		return null;
	}
	
	/**
	 * Returns the number of child nodes
	 */
	public int getChildCount() {
		return 0;
	}
	
	/**
	 * Returns true if this is a leaf node
	 */
	public boolean isLeaf() {
		return true;
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
		return false;
	}
	
	/**
	 * Returns child node with index childIndex
	 */
	public TreeNode getChildAt(int childIndex) {
		return null;
	}
	
	/**
	 * Returns the index of specified child node
	 */
	public int getIndex(TreeNode node) {
		return -1;
	}

	public int compareTo(Object o) {
		return this.name.compareTo(((Candidate)o).toString());
	}

	public String getName() {
		return this.toString();
	}

	public void setName(String name) {
		this.name=name;
	}

	public void removeNodeAt(int x) {
		// TODO Auto-generated method stub
		
	}

	/**
	 * Returns a SQL INSERT statement for this candidate
	 */
	public StringBuffer toSQL() {
		
		//The result variable
		StringBuffer result = new StringBuffer();
		
		//First the candidate
		result.append("INSERT INTO candidates (candidate_id, candidate_name) VALUES (");
		
		//Find the next candidate ID number
		int newCandidateID = 0;
		//For all other elections...
		for(int e=0; e < ((Election)((Race)this.parent).parent).parent.getIndex(this); e++) {
			
			//The current election
			Election currentElection = (Election)((Election)((Race)this.parent).parent).parent.getChildAt(e);
			
			//Add the candidates in this election
			newCandidateID += currentElection.getNumberOfCandidates();
			
		}
		
		//All other races in this election
		Election currentElection = (Election)((Race)this.parent).parent;
		for(int r = 0; r < currentElection.getIndex((Race)this.parent); r++) {
			//For each race...
			
			//The current race
			Race currentRace = (Race)currentElection.getChildAt(r);
			
			//Add the number of candidates in this race to the new candidate id number
			newCandidateID += currentRace.getChildCount();
			
		}
		
		//The order number in this race
		newCandidateID += ((Race)this.parent).getIndex(this);

		result.append(newCandidateID + ", ");
		result.append("'" + this.name + "'");
		result.append(");\n");
		
		//Then the connection race -> candidate
		result.append("INSERT INTO candidateraces (election_id, race_id, candidate_id) VALUES (");
		result.append(((Election)((Race)this.parent).parent).parent.getIndex((Election)((Race)this.parent).parent) + ", ");
		result.append(((Election)((Race)this.parent).parent).getIndex((Race)this.parent) + ", ");
		result.append(newCandidateID);
		result.append(");");
		
		//Okay done, return
		return result;
		
	}

}
