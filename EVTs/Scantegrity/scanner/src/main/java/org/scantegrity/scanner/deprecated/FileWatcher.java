/*
 * Scantegrity - Successor to Punchscan, a High Integrity Voting System
 * Copyright (C) 2006  Richard Carback, David Chaum, Jeremy Clark, 
 * Aleks Essex, Stefan Popoveniuc, and Jeremy Robin
 * 
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */

package org.scantegrity.scanner.deprecated;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.util.Vector;

public class FileWatcher extends Thread {
	
	String dir;
	Vector<ActionListener> objectsThatAreListeningToThis = new Vector<ActionListener>();
	
	boolean running  = false;
	boolean scannNewFilesOnly=true;
	
	public FileWatcher(String dir) {
		this.dir = dir;
	}
	
	public void run() {
		File f = new File(dir);
		if (!f.isDirectory()) {
			return;
		}
		System.out.println("Waiting for ballots to appear in: "+f.getAbsolutePath());
		File[] initialFIles=new File[0];
		if (scannNewFilesOnly)
		 initialFIles = f.listFiles();
		
		running = true;
		Vector<Integer> diff=null;		
		while (running) {
			File[] files = f.listFiles();
			try {
				Thread.sleep(500);
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
			
			if (files.length > initialFIles.length) {
				if ((diff = getFirstDiff(files,initialFIles))!=null)
					for (int j=0;j<diff.size();j++) {
					String filePath = files[diff.get(j)].getAbsolutePath();
					for (int i=0;i<objectsThatAreListeningToThis.size();i++) {
						try {
	/*
							boolean exception = true;
							while (exception) {
								exception = false;
								try {
									ImageIO.read(new File(filePath));
								} catch (IOException e) {
									exception = true;
									try {
										Thread.sleep(2000);
									} catch (InterruptedException e1) {
										e1.printStackTrace();
									}								
								}
							}
	*/						
							objectsThatAreListeningToThis.get(i).actionPerformed(new ActionEvent(this,0,filePath));
						} catch(Exception ex) {
							ex.printStackTrace();
						}
					}
				}
			}
			initialFIles = files;			
		}
		
	}
	
	public void addActionListner(ActionListener a) {
		objectsThatAreListeningToThis.add(a);
	}	
	
	public Vector<Integer> getFirstDiff(File[] newFiles,File[] oldFiles) {
		Vector<Integer> ret = new Vector<Integer>();
		boolean found = false;
		for (int i=0;i<newFiles.length;i++) {
			found=false;
			for (int j=0;j<oldFiles.length;j++) {
				if (newFiles[i].getAbsolutePath().compareTo(oldFiles[j].getAbsolutePath())==0) {
					found=true;
					j=oldFiles.length;
				}
			}
			if (!found)
				ret.add(i);
		}
		return ret;
	}
	
	
	
	public boolean isRunning() {
		return running;
	}

	public void setRunning(boolean running) {
		this.running = running;
	}

	public boolean isScannNewFilesOnly() {
		return scannNewFilesOnly;
	}

	public void setScannNewFilesOnly(boolean scannNewFilesOnly) {
		this.scannNewFilesOnly = scannNewFilesOnly;
	}

	public static void main(String[] args) {
		FileWatcher fw = new FileWatcher("tempImages/");
		fw.start();
	}

}
