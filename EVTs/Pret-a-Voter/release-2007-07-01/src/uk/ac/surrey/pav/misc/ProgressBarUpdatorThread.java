package uk.ac.surrey.pav.audit;

import javax.swing.JProgressBar;

public class ProgressBarUpdatorThread extends Thread {

	private Auditor auditor;
	
	private JProgressBar totalProgressBar;
	
	private JProgressBar partProgressBar;
	
	public void run() {
		
		while(true) {

			//Update the progress bars
			totalProgressBar.setValue(this.auditor.getProgressTotalFinished());
			totalProgressBar.setString("Total progress (" + this.auditor.getProgressTotalFinished() + "%)");
			partProgressBar.setValue(this.auditor.getProgressPartFinished());
			partProgressBar.setString(this.auditor.getProgressPartDescription() + " (" + this.auditor.getProgressPartFinished() + "%)");
		
			//Sleep
			try {
				this.sleep(10);
			} catch (InterruptedException ex) {}
		
		}
		
	}
	
	public ProgressBarUpdatorThread(Auditor auditor, JProgressBar totalProgressBar, JProgressBar partProgressBar) {
		this.auditor = auditor;
		this.totalProgressBar = totalProgressBar;
		this.partProgressBar = partProgressBar;
	}

}
