package uk.ac.surrey.pav.administrator;

import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.ObjectInputStream;
import java.io.PrintStream;
import java.security.PrivateKey;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.Iterator;

import javax.swing.JDialog;
import javax.swing.JFileChooser;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JProgressBar;

import uk.ac.surrey.pav.administrator.treenodes.Election;
import uk.ac.surrey.pav.administrator.treenodes.Race;
import uk.ac.surrey.pav.administrator.treenodes.Root;
import uk.ac.surrey.pav.administrator.treenodes.Teller;
import uk.ac.surrey.pav.ballotform.BallotForm;
import uk.ac.surrey.pav.ballotform.BallotFormPaper;
import uk.ac.surrey.pav.common.interfaces.CSVable;
import uk.ac.surrey.pav.common.interfaces.SQLable;

/**
 * The thread that creates the ballot forms
 * 
 * @author David Lundin
 *
 */
public class BallotFormCreator implements Runnable {

	JDialog contentPane;
	
	Root rootNode;
	
	JProgressBar progressBar;
	
	BallotFormCreator(JDialog contentPane, Root rootNode, JProgressBar progressBar) {
		this.contentPane = contentPane;
		this.rootNode = rootNode;
		this.progressBar = progressBar;
	}
	
	public void run() {
		
		try {
			
			/*
			 * Load a private key to sign with
			 */

			//Open a file
			JOptionPane.showMessageDialog(null, "Please select a file which contains your private key.", "Load private key", JOptionPane.INFORMATION_MESSAGE);
			JFileChooser jfc = new JFileChooser();
			if(jfc.showOpenDialog(this.contentPane) == JFileChooser.APPROVE_OPTION) {
				
				//Load private key
				ObjectInputStream objectIn = new ObjectInputStream(new FileInputStream(jfc.getSelectedFile()));
				PrivateKey privateKey = ((PrivateKey)objectIn.readObject());
	
				//Counts the ballot form papers
				int ballotFormPaperID = Integer.parseInt(JOptionPane.showInputDialog(this.contentPane, "Please enter the first BALLOT FORM PAPER serial number?", "Question", JOptionPane.QUESTION_MESSAGE));
				
				//A list of all the ballot form papers
				ArrayList ballotFormPaperList = new ArrayList();

				//Ballot form serial numbers
				int ballotFormSerialNo = Integer.parseInt(JOptionPane.showInputDialog(this.contentPane, "What is the first BALLOT FORM serial number?", "Question", JOptionPane.QUESTION_MESSAGE));

				//Open a file for the CSV data
				JOptionPane.showMessageDialog(null, "Please specify a file in which to save the CSV data of the ballot forms.", "Save", JOptionPane.INFORMATION_MESSAGE);
				jfc = new JFileChooser();
				if(jfc.showOpenDialog(this.contentPane) == JFileChooser.APPROVE_OPTION) {

					//Open file
					FileOutputStream fosCSV;
					fosCSV = new FileOutputStream(jfc.getSelectedFile());
					PrintStream pCSV = new PrintStream(fosCSV);
					
					//Open a file for the SQL data
					JOptionPane.showMessageDialog(null, "Please specify a file in which to save the SQL data of the ballot forms.", "Save", JOptionPane.INFORMATION_MESSAGE);
					jfc = new JFileChooser();
					if(jfc.showOpenDialog(this.contentPane) == JFileChooser.APPROVE_OPTION) {
	
						//Open file
						FileOutputStream fosSQL;
						fosSQL = new FileOutputStream(jfc.getSelectedFile());
						PrintStream pSQL = new PrintStream(fosSQL);

						//A list of all the ballot forms
						ArrayList ballotFormList = new ArrayList();
						
						//Get the elections
						Enumeration e = rootNode.getChildAt(3).children();
						
						//Check serial number is at least 1
						if(ballotFormPaperID >= 1 && ballotFormSerialNo >= 1) {

							//For each election
							while(e.hasMoreElements()) {
								
								//The current election
								Election currentElection = (Election)e.nextElement();
								
								//Get the number of ballot forms to create
								int numberOfBallotForms = Integer.parseInt(JOptionPane.showInputDialog(this.contentPane, "Please enter the number of ballot forms to print:", "Question", JOptionPane.QUESTION_MESSAGE));
								
								//Check that we have at least one ballot form to print
								if(numberOfBallotForms > 0) {
									
									//Set the progress bar text
									progressBar.setString("Creating ballot forms");
									
									//Now create that number of ballot forms
									for(int x = 0; x < numberOfBallotForms; x++) {
										
										//Create a new ballot form paper
										BallotFormPaper currentBallotFormPaper = new BallotFormPaper(ballotFormPaperID++);
										
										//Get the races
										Enumeration r = currentElection.children();
										
										//For each race
										while(r.hasMoreElements()) {
											
											//The current race
											Race currentRace = (Race)r.nextElement();
											
											//Create a ballot form
											BallotForm currentBallotForm = new BallotForm(ballotFormSerialNo++, currentRace.getChildCount(), currentElection.parent.getIndex(currentElection), currentElection.getIndex(currentRace));
											
											//Get the tellers
											Enumeration t = rootNode.getChildAt(0).children();
											
											//For each teller
											while(t.hasMoreElements()) {
												
												//The current teller
												Teller currentTeller = (Teller)t.nextElement();
												
												//Add two layers of encryption for this teller
												currentBallotForm.addLayerToOnion(currentTeller.getPublicKey());
												currentBallotForm.addLayerToOnion(currentTeller.getPublicKey());

											}

											//Sign the ballot form
											currentBallotForm.sign(privateKey);

											//Store reference to form
											//ballotFormList.add(currentBallotForm);
											
											//Store ballot form in paper
											currentBallotFormPaper.addForm(currentBallotForm);
											
										}

										//Sign ballot form paper
										currentBallotFormPaper.signHash(privateKey);
										
										//Store reference to paper
										//ballotFormPaperList.add(currentBallotFormPaper);
										
										//Store the ballot form CSV
										pCSV.print(currentBallotFormPaper.toCSV());
										
										//Store the ballot form SQL
										pSQL.print(currentBallotFormPaper.toSQL());

										//Update the progress bar
										int newValue = (int)(100*(x+1) / numberOfBallotForms);
										progressBar.setValue(newValue);
										progressBar.setString("Creating ballot forms (" + newValue + "%)");


									}
									
								}
								
							}

						} else {
							
							//Serial no below zero
							JOptionPane.showMessageDialog(null, "The first ballot form serial number must be at least 1.", "Invalid serial number", JOptionPane.ERROR_MESSAGE);

						}
	
						//Close the file
						pSQL.close();
					
					}

					//Close the file
					pCSV.close();
				
				}

			}
			
			//Close the dialog
			this.contentPane.setVisible(false);
			
	    } catch (Exception ex) {
	    	ex.printStackTrace();
	    }
		
	}

}
