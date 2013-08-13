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

import java.awt.BorderLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.lang.Thread.UncaughtExceptionHandler;
import java.util.ArrayList;

import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JFileChooser;
import javax.swing.JLabel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.filechooser.FileFilter;

import sexpression.ASExpression;
import sexpression.stream.ASEInputStreamReader;
import sexpression.stream.InvalidVerbatimStreamException;

/**
 * Tool which parses the output of Launcher run VoteBox sessions and displays the "ballot result"
 * using the appropriate graphics.
 * 
 * Simplifies determining results.
 * 
 * @author Montrose
 *
 */
public class BallotResultParser {

	ArrayList<RaceResult> races;
	
	/**
	 * Parses a log file for the results of the race.
	 * 
	 * @param infile - log file
	 */
	public void parseFile(File infile){
		ASEInputStreamReader reader=null;
		ASExpression dat=null;
		
		InputStream in=null;
		//setup input stream
		try{
			in = new FileInputStream(infile);
		}catch(FileNotFoundException e){
			try{
				System.out.println("Trying lower case: "+ infile.getParent() +File.separator + infile.getName().toLowerCase() +"("+infile.getName()+")");
				infile=new File(infile.getParent() +File.separator +infile.getName().toLowerCase());
				in=new FileInputStream(infile);
			}catch(FileNotFoundException f){
			System.out.println("Could not find file: "+ infile);
			return;
			}
		}
		
		reader = new ASEInputStreamReader(in);
		
		int available=0;
		try{
			available=in.available();
		}catch(IOException e){}
		
		if(available!=0){
			try{
				dat=reader.read();
				available=in.available();
			}
			catch(InvalidVerbatimStreamException e){System.out.println("FAIL: Invalid Verbatim Stream: " + e.getMessage());}
			catch(IOException e){System.out.println("FAIL: IO exception: "+ e.getMessage());}
			//System.out.println(dat);
			races= RaceResult.parseRaces(dat);
		}
	}
	
	/**
	 * @return List of RaceResults.
	 */
	public ArrayList<RaceResult> getVotes(){
		return races;
	}

	/**
	 * Usage:
	 * 	java actionparser.BallotResultParser [log file] [ballot file]
	 * 
	 * Any ommitted arguments will be prompted for.
	 * 
	 * @param args - runtime arguments
	 */
	public static void main(String[] args) {
		Thread.setDefaultUncaughtExceptionHandler(new UncaughtExceptionHandler(){
			public void uncaughtException(Thread t, Throwable e) {
				final JDialog dialog = new JDialog();
				dialog.setTitle("An unexpected error occured");
				dialog.setSize(800,600);
				dialog.setLayout(new BorderLayout());
				dialog.add(new JLabel("Please include the following as well as the involved _ballot & .zip files in a bug report."), BorderLayout.NORTH);
				
				JTextArea area = new JTextArea();
				StringWriter writer = new StringWriter();
				e.printStackTrace(new PrintWriter(writer));
				
				area.setText(writer.toString());
				area.setEditable(false);
				
				dialog.add(new JScrollPane(area), BorderLayout.CENTER);
				
				JButton done = new JButton("Done, Exit Program");
				
				dialog.add(done, BorderLayout.SOUTH);
				
				done.addActionListener(new ActionListener(){
					public void actionPerformed(ActionEvent e) {
						dialog.setVisible(false);
						System.exit(-1);
					}
				});
				
				dialog.setModal(true);
				dialog.setDefaultCloseOperation(JDialog.DO_NOTHING_ON_CLOSE);
				dialog.setVisible(true);
			}
		});
		
		BallotResultParser bp=new BallotResultParser();
		
		File log = null;
		File ballot = null;
		
		if(args.length >= 1)
			log = new File(args[0]);
		
		if(args.length >= 2)
			ballot = new File(args[1]);
		
		if(args.length >= 3){
			System.out.println("Usage:\n\tjava actionparser.BallotResultParser [log file] [ballot file]");
			System.exit(-1);
		}
		
		JFileChooser chooser = new JFileChooser();
		
		if(log == null){
			chooser.setDialogTitle("Select log file");
			int ret = chooser.showOpenDialog(null);
			
			if(ret != JFileChooser.APPROVE_OPTION)
				return;
			
			log = chooser.getSelectedFile();
		}
		
		if(ballot == null){
			chooser.setDialogTitle("Select ballot (.zip) file");
			chooser.setFileFilter(new FileFilter(){
				@Override
				public boolean accept(File f) {
					return f.isDirectory() || f.getName().toLowerCase().endsWith(".zip");
				}

				@Override
				public String getDescription() {
					return "Ballot (.zip) Files";
				}
			});
			
			int ret = chooser.showOpenDialog(null);
			
			if(ret != JFileChooser.APPROVE_OPTION)
				return;
			
			ballot = chooser.getSelectedFile();
		}
		
		if(!log.exists()){
			System.out.println("Log file \""+log+"\" cannot be found.");
			System.exit(-1);
		}
		
		if(!ballot.exists()){
			System.out.println("Ballot file \""+ballot+"\" cannot be found");
			System.exit(-1);
		}
		
		bp.parseFile(log);
		
		(new ResultView(bp.getVotes(), ballot)).setVisible(true);
	}

}
