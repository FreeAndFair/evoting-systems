package uk.ac.surrey.pav.bulletinboard.batches;

import javax.swing.JLabel;
import javax.swing.JProgressBar;

/**
 * Updates the batch creator dialog, mainly the progress bar
 * 
 * @author David Lundin
 *
 */
public class BatchCreatorUpdatorThread extends Thread {

	/**
	 * The creator doing the creating
	 */
	private BatchCreator creator;
	
	/**
	 * The progress bar to update
	 */
	private JProgressBar progressBar;
	
	/**
	 * A label setting out current action
	 */
	private JLabel progressLabel;
	
	/**
	 * Dialog window to close when finished
	 */
	private BatchCreatorDialog progressDialog;
	
	public BatchCreatorUpdatorThread(BatchCreator creator) {
		//Store the references
		this.creator = creator;
	}
	
	/**
	 * The work this thread does
	 */
	public void run() {
		
		//Show a dialog box
		this.progressDialog = new BatchCreatorDialog(this.creator);
		this.progressDialog.setVisible(true);
		this.progressBar = this.progressDialog.getProgressBar();
		this.progressLabel = this.progressDialog.getProgressLabel();

		while(this.creator.isWorking()) {
			
			//Update the progress bar
			this.progressBar.setValue(this.creator.getPercentageDone());
			this.progressLabel.setText(this.creator.getCurrentAction());
			
			//Sleep for a bit
			try {
				Thread.sleep(100);
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
		}
		
		//Close the window
		this.progressDialog.setVisible(false);
		
	}
	
}
