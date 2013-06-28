package uk.ac.surrey.pav.bulletinboard.statclient;

import java.util.ArrayList;

public class StatCollection {

	public ArrayList statistics = new ArrayList();
	
	public Statistic getMostRecent() {
		if(this.statistics.size() > 0) {
			return (Statistic)this.statistics.get(this.statistics.size() - 1);
		} else {
			return null;
		}
	}
	
}
