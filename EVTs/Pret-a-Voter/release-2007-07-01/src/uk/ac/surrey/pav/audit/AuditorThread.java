package uk.ac.surrey.pav.audit;

/**
 * Thread in which the auditor tuns
 * 
 * @author David Lundin
 *
 */
public class AuditorThread extends Thread {

	private Auditor auditor;
	
	public void run() {
		this.auditor.auditAll();
	}
	
	public AuditorThread(Auditor auditor) {
		this.auditor = auditor;
	}
	
}
