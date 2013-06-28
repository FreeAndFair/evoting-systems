package uk.ac.surrey.pav.bulletinboard.statclient;

import java.sql.Timestamp;

public class Statistic {

	public Timestamp timeStamp;
	
	public int postedVotes;
	
	public int auditedForms;

	public Statistic(Timestamp timeStamp, int postedVotes, int auditedForms) {
		this.timeStamp = timeStamp;
		this.postedVotes = postedVotes;
		this.auditedForms = auditedForms;
	}
	
}
