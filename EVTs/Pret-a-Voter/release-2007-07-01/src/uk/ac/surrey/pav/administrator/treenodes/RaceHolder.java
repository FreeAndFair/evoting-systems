package uk.ac.surrey.pav.administrator.treenodes;

import java.io.Serializable;

/**
 * Holds a race with the associated election and race IDs
 * 
 * @author David Lundin
 *
 */
public class RaceHolder implements Serializable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	private Race race;
	private int eid;
	private int rid;
	
	/**
	 * 
	 * @param race Race to hold
	 * @param eid Election id
	 * @param rid Race id
	 */
	public RaceHolder(Race race, int eid, int rid){
		this.race = race;
		this.eid = eid;
		this.rid = rid;
	}

	public int getEid() {
		return eid;
	}

	public void setEid(int eid) {
		this.eid = eid;
	}

	public Race getRace() {
		return race;
	}

	public void setRace(Race race) {
		this.race = race;
	}

	public int getRid() {
		return rid;
	}

	public void setRid(int rid) {
		this.rid = rid;
	}
}
