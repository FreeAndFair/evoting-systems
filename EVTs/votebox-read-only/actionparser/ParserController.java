/**
  * This file is part of VoteBox.
  * 
  * VoteBox is free software: you can redistribute it and/or modify
  * it under the terms of the GNU General Public License version 3 as published by
  * the Free Software Foundation.
  * 
  * You should have received a copy of the GNU General Public License
  * along with VoteBox, found in the root of any distribution or
  * repository containing all or part of VoteBox.
  * 
  * THIS SOFTWARE IS PROVIDED BY WILLIAM MARSH RICE UNIVERSITY, HOUSTON,
  * TX AND IS PROVIDED 'AS IS' AND WITHOUT ANY EXPRESS, IMPLIED OR
  * STATUTORY WARRANTIES, INCLUDING, BUT NOT LIMITED TO, WARRANTIES OF
  * ACCURACY, COMPLETENESS, AND NONINFRINGEMENT.  THE SOFTWARE USER SHALL
  * INDEMNIFY, DEFEND AND HOLD HARMLESS RICE UNIVERSITY AND ITS FACULTY,
  * STAFF AND STUDENTS FROM ANY AND ALL CLAIMS, ACTIONS, DAMAGES, LOSSES,
  * LIABILITIES, COSTS AND EXPENSES, INCLUDING ATTORNEYS' FEES AND COURT
  * COSTS, DIRECTLY OR INDIRECTLY ARISING OUR OF OR IN CONNECTION WITH
  * ACCESS OR USE OF THE SOFTWARE.
 */

package actionparser;

import java.awt.*;
import java.io.*;
import java.util.Date;

import javax.swing.*;
import javax.swing.filechooser.FileFilter;


public class ParserController {
	
	public void parseDirectory(String input, String output, String outname, String configPath) throws IOException{
		ActionParser ap=new ActionParser();
		BallotResultParser bp=new BallotResultParser();
		
		
		FilenameFilter ff=new FilenameFilter(){
			//do not get ballot logs
			public boolean accept(File dir,String name){
				if(name.indexOf("_ballot")==-1) return true;
				else return false;
			}
		};
		
		//verify input directory
		File indir=new File(input);
		if(!indir.isDirectory())
			throw new IOException("Invalid input directory path: "+input);
		
		//create/verify output directory
		File outdir=new File(output);
		if(outdir.exists()&&!outdir.isDirectory())
			throw new IOException("Output path must be a directory: "+output);
		else if(!outdir.exists())
			outdir.mkdir();
		
		
		File[] files=indir.listFiles(ff);
		File summary=new File(output+File.separator+outname+"-summary.csv");
		PrintStream summaryStream=null;
		String detailOutFile=null;
		
		//open the stream to the summary output file
		try{
			if(summary!=null)
				summaryStream = new PrintStream(summary);
			else
				summaryStream=System.out;
		}catch(FileNotFoundException e){
			System.out.println("Could not write to file: "+ summary);
		}
		//print summary file columns headers
		summaryStream.println("id,startt,totalt,rev1t,revtott,revtocastt,numrevview,[ballot-results]");
		
		//iterate over files
		for(File f: files){	
			//out.println(f.getName());
			//parse actions
			detailOutFile=output+File.separator+outname+"-"+f.getName()+".csv";
			ap.parseFile(f.getPath(), detailOutFile,configPath);
			//parse results
			bp.parseFile(new File(f.getPath()+"_ballot"));
			//output
			printOutputLine(f,ap,bp,summaryStream);
		}
	}	
	
	/**
	 * prints the output corresponding to the parsed data files provided
	 * @param ap the parsed action data
	 * @param bp the parsed ballot data
	 * @param dest the stream to print to
	 */
	private void printOutputLine(File input, ActionParser ap, BallotResultParser bp, PrintStream dest) {
		dest.print(input.getName()+",");//Subject ID
		dest.print(new Date(ap.getStartTime()).toString()+",");//Expt start time
		dest.print(ap.getTotalTime()+",");//total time
		dest.print(ap.getFirstPageView(ap.getReviewPage()).getTotalTime()+",");//first time review
		dest.print(ap.getTotalPageTime(ap.getReviewPage())+",");//total time on review
		dest.print(ap.getEndTime()-ap.getFirstPageView(ap.getReviewPage()).getStartTime()+",");//time from review to cast
		dest.print(ap.getPageViews(ap.getReviewPage()));//# review screen views
		for(RaceResult r: bp.getVotes()){
			dest.print(","+r.get_res().get(0));
		}
		dest.println();
	}
	
	public void buildGUI(){
		final JFrame frame =new JFrame("VoteBox Log Parser");
		
		frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		
		JLabel inpLabel=new JLabel("Input directory (The log file location):");
		JLabel outLabel=new JLabel("Output directory (Where to write the results):");
		JLabel nameLabel=new JLabel("Base output name (What to call the output files):");
		JLabel ballotLabel=new JLabel("Config directory (Where to find the layout files):");
		
		
		final JTextField inpField = new JTextField(50);
		inpField.setEditable(false);
		final JTextField outField = new JTextField(50);
		outField.setEditable(false);
		final JTextField ballotField = new JTextField(50);
		ballotField.setEditable(false);
		final JTextField nameField = new JTextField(50);
		
		JButton inpBrowse = new JButton("Browse...");
		
		inpBrowse.addActionListener(new java.awt.event.ActionListener() {
			public void actionPerformed(java.awt.event.ActionEvent e) {
				inpField.setText(getDir(frame));
			}
		});
		
		JButton outBrowse = new JButton("Browse...");
		
		outBrowse.addActionListener(new java.awt.event.ActionListener() {
			public void actionPerformed(java.awt.event.ActionEvent e) {
				outField.setText(getDir(frame));
			}
		});
		
		JButton ballotBrowse = new JButton("Browse...");
		
		ballotBrowse.addActionListener(new java.awt.event.ActionListener() {
			public void actionPerformed(java.awt.event.ActionEvent e) {
				ballotField.setText(getDir(frame));
			}
		});
		
		JButton startButton=new JButton("Start");
		
		startButton.addActionListener(new java.awt.event.ActionListener() {
			public void actionPerformed(java.awt.event.ActionEvent e) {
				String input=inpField.getText();
				String output=outField.getText();
				String ballot=ballotField.getText();
				String name=nameField.getText();
				if(	input.length()!=0 &&
					output.length()!=0 &&
					name.length()!=0 &&
					ballot.length()!=0){
					ParserController pc=new ParserController();
					try{
						
						pc.parseDirectory(input,output,name,ballot);
						JOptionPane.showMessageDialog(frame, "Parsing complete: output written to " + output);
						System.exit(0);
					}catch(IOException f){
						JOptionPane.showMessageDialog(frame, "Bad input directory");
					}catch(Exception g){
						System.err.print(g.getMessage());
						g.printStackTrace();
						JOptionPane.showMessageDialog(frame, "An unhandled exception has been encountered.  This is typically due to incorrect inputs, such as non-log files located in the input directory.\nPlease check the terminal for additional error output.\n\nIf this is not the case, please contact the maintatiner, Michael O'Connor, at moconnor@rice.edu to report this problem.");
					}
					
				}else{
					JOptionPane.showMessageDialog(frame, "Please enter values for all parameters.");
				}
			}
		});
		
		JPanel content=new JPanel(new GridLayout(8,2));
		Container cp=frame.getContentPane();
		cp.setLayout(new BorderLayout());
		
		content.add(inpLabel);content.add(new JPanel());
		content.add(inpField);content.add(inpBrowse);
		content.add(outLabel);content.add(new JPanel());
		content.add(outField);content.add(outBrowse);
		content.add(ballotLabel);content.add(new JPanel());
		content.add(ballotField);content.add(ballotBrowse);
		content.add(nameLabel);content.add(new JPanel());
		content.add(nameField);content.add(new JPanel());
		
		cp.add(content, BorderLayout.CENTER);
		cp.add(startButton, BorderLayout.SOUTH);	
		
		frame.validate();
		frame.setSize(650,400);
		frame.setVisible(true);
	}
	
	
	private String getDir(Component parent){
		JFileChooser chooser = new JFileChooser();
		chooser.setFileFilter(new FileFilter() {

			@Override
			public boolean accept(File arg0) {
				return arg0.isDirectory();
			}

			@Override
			public String getDescription() {
				return "Directories";
			}
		});
		chooser.setFileSelectionMode(JFileChooser.DIRECTORIES_ONLY);
		int returnVal = chooser.showOpenDialog(parent);
		if (returnVal == JFileChooser.APPROVE_OPTION)
			return chooser.getSelectedFile().getAbsolutePath();
		return "";
	}
	
	
	/**
	 * @param args
	 */
	public static void main(String[] args) {
	ParserController pc=new ParserController();
		if(args.length==0){
			pc.buildGUI();
		}
		else if(args.length<3){
			System.out.println("ParserController requires four parameters: input-dir output-dir ballot-dir base-output-name");
			System.exit(1);
		}else{
		
		try{
			pc.parseDirectory(args[0],args[1],args[3],args[2]);
		}catch(IOException e){
			System.out.println("Bad input directory");
		}
		}

	}

}
