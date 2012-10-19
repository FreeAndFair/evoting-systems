package org.scantegrity.erm;

import java.awt.BorderLayout;
import java.awt.Component;
import java.awt.Font;

import javax.swing.JPanel;
import javax.swing.JButton;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.SwingWorker;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Scanner;

public class TallyPanel extends JPanel {

	private static final long serialVersionUID = 1L;
	WriteInResolver c_resolver = null;
	String c_path = null;
	private JButton jButton = null;
	private JScrollPane resultsPane = null;
	private JTextArea resultsText = null;
	private WriteInResolver c_spoiledResolver = null;
	private ErrorBallotResolver c_errorResolver = null;

	/**
	 * This is the default constructor
	 */
	public TallyPanel(WriteInResolver p_resolver, WriteInResolver p_spoiledResolver, 
			ErrorBallotResolver p_errorResolver, String p_path) {
		super();
		c_path = p_path;
		c_resolver = p_resolver;
		c_errorResolver = p_errorResolver; 
		c_spoiledResolver = p_spoiledResolver;
		initialize();
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(500, 275);
		this.setLayout(new BorderLayout());
		this.add(getResultsPane(), BorderLayout.CENTER);
		this.add(getJButton(), BorderLayout.SOUTH);
	}

	private Component getResultsPane() {		
		if(resultsText == null) {
			resultsText = new JTextArea(); 
		}
		
		if(resultsPane == null) {
			resultsPane = new JScrollPane(resultsText);
		}
	
		resultsText.setText("Please click the Tally button below to generate results.");
		
		return resultsPane;
	}
	
	/**
	 * This method initializes jButton	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButton() {
		if (jButton == null) {
			jButton = new JButton();
			jButton.setText("Tally");
			jButton.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					SwingWorker<Void, Void> l_worker = new SwingWorker<Void, Void>(){

						@Override
						protected Void doInBackground() throws Exception {
							c_resolver.disableTabs();
							System.out.println("Tallying....");
							c_resolver.Tally(c_path);
							System.out.println("Writing Results Files....");
							c_resolver.WriteResults(c_path);
							System.out.println("Writing Write-in Resolution PDF...");
							c_resolver.WriteResolutionPdf(c_path);
							c_errorResolver.disableTabs(); 
							//c_errorResolver.Tally(c_path); 
							//c_errorResolver.WriteResults(c_path);  
							System.out.println("Writing Error Resolution PDF...");
							c_errorResolver.WriteResolutionPdf(c_path); 
							System.out.println("Writing Spoiled Results...");
							c_spoiledResolver.WriteResults(c_path);
							System.out.println("Complete. Showing Results Now.");
							showResults(); 
							return null;
						}

						@Override
						protected void done()
						{
							jButton.setText("Done");
						}
						
					};
					jButton.setText("Processing");
					jButton.setEnabled(false);
					l_worker.execute();
				}
			});
		}
		return jButton;
	}

	private void showResults() {
		Scanner scanner = null;
		File resultsFile = new File(c_path + File.separator + "Results" + File.separator + "resolved-results.txt");
		if(!resultsFile.exists()) {
			resultsText.setText("Could not find the results file.");
			return;
		}
		
		try {
			scanner = new Scanner(resultsFile);
		} catch (FileNotFoundException e) {
			System.out.println("Could not open the results file.");
		}
		
		String results = "";
		
		while(scanner.hasNext()) {
			results += scanner.nextLine() + "\n";
		}
		
		resultsText.setFont(new Font("Courier New", Font.BOLD, 12));
		resultsText.setText(results);
	}

}
