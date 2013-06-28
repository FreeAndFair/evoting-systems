package uk.ac.surrey.pav.administrator.treenodes;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Enumeration;

import javax.swing.tree.TreeNode;

/**
 * Keeps a list of the elections and sets this out in the GUI JTree
 * 
 * @author David Lundin
 *
 */
public class ElectionNode implements ChildRemovableTreeNode, Serializable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The elections currently being set up
	 */
	private ArrayList elections = new ArrayList();
	
	/**
	 * Parent root node
	 */
	private Root parent;

	/**
	 * Gets an election at a particular place in the list
	 */
	public TreeNode getChildAt(int childIndex) {
		return (TreeNode) elections.get(childIndex);
	}

	/**
	 * The number of elections in the list
	 */
	public int getChildCount() {
		return elections.size();
	}

	/**
	 * Returns reference to the parent Root element
	 */
	public TreeNode getParent() {
		return this.parent;
	}

	/**
	 * Returns the index of a particular election
	 */
	public int getIndex(TreeNode node) {
		for (int x = 0; x < elections.size(); x++) {
			if (elections.get(x) == node)
				return x;
		}
		return -1;
	}

	/**
	 * Allows children
	 */
	public boolean getAllowsChildren() {
		return true;
	}

	/**
	 * Is never a leaf
	 */
	public boolean isLeaf() {
		if(this.elections.size() > 0) {
			return false;
		} else {
			return true;
		}
	}

	/**
	 * All the elections in the list
	 */
	public Enumeration children() {
		return Collections.enumeration(this.elections);
	}
	
	/**
	 * Constructor
	 * 
	 * @param parent
	 */
	public ElectionNode(Root parent) {

		//Store reference to parent
		this.parent = parent;
		
		//Create an election
		//TODO: These are not the correct start and end dates
		/*Election e = new Election("2007 Surrey Election", this, Date.valueOf("2007-01-01"), Date.valueOf("2007-12-31"));

		Race president = new Race("Union President",e);
		president.addCandidate(new Candidate("Michael Aton",president));
		president.addCandidate(new Candidate("Reopen Nominations (RON)",president));
		president.addCandidate(new Candidate("Alex Collins",president));
	
		Race vpSports = new Race("VP Sports and Recreation",e);
		vpSports.addCandidate(new Candidate("Reopen Nominations (RON)",vpSports));
		vpSports.addCandidate(new Candidate("Steve Cottingham",vpSports));
		vpSports.addCandidate(new Candidate("Nagre Narendrasing",vpSports));
		vpSports.addCandidate(new Candidate("Gemma Leaming",vpSports));
		
		Race vpSocieties = new Race("VP Societies and Individual Development",e);
		vpSocieties.addCandidate(new Candidate("Madiha Latif",vpSocieties));
		vpSocieties.addCandidate(new Candidate("Mark Griffiths",vpSocieties));
		vpSocieties.addCandidate(new Candidate("Reopen Nominations (RON)",vpSocieties));
		
		Race vpEducation = new Race("VP Education",e);
		vpEducation.addCandidate(new Candidate("Reopen Nominations (RON)",vpEducation));
		vpEducation.addCandidate(new Candidate("Mike Blakeney",vpEducation));
		
		Race vpWelfare = new Race("VP Welfare",e);
		vpWelfare.addCandidate(new Candidate("Reopen Nominations (RON)",vpWelfare));
		vpWelfare.addCandidate(new Candidate("Sophia Hawkins",vpWelfare));
		
		Race questionNUS = new Race("Should the Student Union continue its membership with the National Union of Students (NUS)?",e);
		questionNUS.addCandidate(new Candidate("Yes",questionNUS));
		questionNUS.addCandidate(new Candidate("No",questionNUS));
		
		Race questionFairtrade = new Race("Do you agree with the University\\'s Fairtrade Policy and support the University\\'s effort towards attaining Fairtrade University status?",e);
		questionFairtrade.addCandidate(new Candidate("Yes",questionFairtrade));
		questionFairtrade.addCandidate(new Candidate("No",questionFairtrade));
		
		e.addRace(president);
		e.addRace(vpSports);
		e.addRace(vpSocieties);
		e.addRace(vpEducation);
		e.addRace(vpWelfare);
		e.addRace(questionNUS);
		e.addRace(questionFairtrade);
		
		this.addElection(e);*/

	}

	/**
	 * Add a new election to the list
	 * 
	 * @param e The election to be added
	 */
	public void addElection(Election e) {
		this.elections.add(e);
	}

	/**
	 * Removes a particular election from the list
	 */
	public void removeNodeAt(int x) {
		elections.remove(x);		
	}

	/**
	 * Returns the name of the node
	 */
	public String getName() {
		return this.toString();
	}

	/**
	 * Sorts the elections in alphabetical order
	 */
	public void reorder() {
		// TODO Auto-generated method stub
	}

	/**
	 * Not applicable
	 */
	public void setName(String name) {
	}
	
	/**
	 * Returns the arraylist of the elections
	 * 
	 * @return An ArrayList of all the elections
	 */
	public ArrayList getElections(){
		return this.elections;
	}
	
	/**
	 * Returns string representation of the node
	 */
	public String toString() {
		return "Elections";
	}

	/**
	 * Removes a particular child
	 */
	public void removeChild(Object child) {
		this.elections.remove(child);
	}

}
