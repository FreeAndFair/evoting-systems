/**
 * @(#)ScannerController.java 
 *  
 * Created By: carback1
 * Date: Oct 7, 2009
 * Copyright (C) 2008 Scantegrity Project
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
package org.scantegrity.scanner;

import java.awt.image.BufferedImage;
import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Arrays;
import java.util.Vector;
import java.util.logging.Level;
import java.util.logging.Logger;
import javax.imageio.ImageIO;
import javax.media.jai.JAI;
import javax.media.jai.RenderedOp;

import static org.apache.commons.io.IOUtils.closeQuietly;

import org.apache.commons.io.FileUtils;
import org.scantegrity.common.Logging;

/**
 * Command line Unix interface to the scanner. 
 * 
 * @author carback1
 *
 */
public class ScannerController {
	private String c_binpath = "/usr/local/bin/";
	private String c_inpath = "/mnt/scantegrityfs/";
	private String c_outpath = "./";
	private String c_scanimgcmd = "scanscript";
	private String c_testopts = "-L";
	private String c_scanopts = "scan-%d.tiff";
	private String c_scanfmt = "scan-%s.tiff";
	private String c_sigcmd = "kill -0 %s";
	private String c_killcmd = "kill -9 %s";
	private String c_pgrep = "pgrep %s";
	private Logging c_log = null;
	private long c_timeout = 3000;
	private long c_hangup = 12000;
	private boolean c_delete = true;
	//Incremented/added to scanfmt and scanopts when unable to delete file...
	private int c_suffix = 0;
	private int c_err = 0;
	
	/**
	 * Default Constructor. 
	 * 
	 * @throws IOException
	 * @throws InterruptedException
	 */
	public ScannerController()
	{
		this(null, null, null, null, false);
	}
	
	/**
	 * Convenience Constructor. Uses defaults with the exception of a log obj.
	 * @param p_log
	 * @throws IOException
	 * @throws InterruptedException
	 */
	public ScannerController(Logging p_log)
	{
		this(p_log, null, null, null, false);
	}
	
	
	/**
	 * Full Constructor. Most of the common options can be set.
	 * 
	 * @param p_log - The logging option.
	 * @param p_binpath - The path to the binaries for the scannercontroller.
	 * @param p_inpath - The path for input (image files). This should be a ramdisk!
	 * @param p_outpath - Where output files should be stored.
	 * @throws IOException
	 * @throws InterruptedException
	 */
	public ScannerController(Logging p_log, String p_binpath, String p_inpath, 
								String p_outpath, boolean p_delete)
	{
		if (p_binpath != null) c_binpath = p_binpath;
		if (p_outpath != null) setOutpath(p_outpath);
		if (p_inpath != null) setInpath(p_inpath);
		
		c_delete = p_delete;
		
		c_log = p_log;		
		if (c_log == null)
		{
			Vector<String> l_out = new Vector<String>();
			l_out.add("");
			c_log = new Logging(l_out, -1,  Level.OFF);
		}
		
		//Can I read/write to the paths?
		//....Assume we can read/write to ""
		try 
		{
			File l_f = new File(p_binpath);
			if (!l_f.exists() || !l_f.isDirectory() || !l_f.canRead())
			{
				p_binpath = "";
			}
		}
		catch (Exception l_e)
		{
			p_binpath = "";
		}
		if (p_binpath == "") 
		{
			c_log.log(Level.WARNING, "Binary path is unusable: " + p_binpath);			
		}
		//input path
		try 
		{
			File l_f = new File(p_inpath);
			if (!l_f.exists() || !l_f.isDirectory() || !l_f.canRead())
			{
				p_inpath = "";
			}
		}
		catch (Exception l_e)
		{
			p_inpath = "";
		}
		if (p_inpath == "")
		{
			c_log.log(Level.WARNING, "In path is unusable: " + p_inpath);
		}
		
		//output path
		try 
		{
			File l_f = new File(p_outpath);
			if (!l_f.exists() || !l_f.isDirectory() || !l_f.canWrite())
			{
				p_outpath = "";
			}
		}
		catch (Exception l_e)
		{
			p_outpath = "";
		}
		if (p_outpath == "")
		{
			c_log.log(Level.WARNING, "Output path is unusable: " + p_outpath);			
		}
	
		try
		{	
			//Test to make sure the command works.
			Process l_p = Runtime.getRuntime().exec(c_binpath + c_scanimgcmd 
													+ " " + c_testopts);
			synchronized(this)
			{
				l_p.waitFor();
				if (l_p.exitValue() != 0)
				{
					String l_err = "Unable to open scanning program. Error: ";
					l_err += getErrorMsg(l_p);
					c_log.log(Level.SEVERE, l_err);
				}
				else
				{
					c_log.log(Level.INFO, "Scanner control initialized and working.");				
				}
				
				closeProcess(l_p); 
			}
		}
		catch (Exception l_e)
		{
			c_log.log(Level.SEVERE, "Unable to start scanning program!" 
						+ l_e.getMessage());
		}
	}
	
	/**
	 * Return a ballot image from the scanner. The scan is in duplex, so this
	 * will always return an array of size 2. The elements inside *may* be null,
	 * however.
	 * 
	 * @return
	 * @throws IOException
	 */
	public BufferedImage[] getImagesFromScanner() throws IOException
	{
		Process l_p;
		int l_pid = 0; 
		String l_cmd = c_binpath + c_scanimgcmd + " " + c_inpath + c_scanopts;
		//Execute the scan command
		l_p = Runtime.getRuntime().exec(l_cmd);
		l_pid = getPid(c_scanimgcmd);
		if (l_pid == 0) 
		{
			try {
				l_p.exitValue();
			}
			catch (IllegalThreadStateException l_e)
			{
				c_log.log(Level.WARNING, c_binpath + c_scanimgcmd 
						+ " failed to exec." + getErrorMsg(l_p));
			}
			l_pid = -1;
		}
		synchronized (this) {
			//Wait for it to end.
			int l_hang = 0;
			do
			{
				for (int l_i = 0; l_i < c_timeout; l_i+=200)
				{
					if (l_pid != getPid(c_scanimgcmd)) break;
					try {
						wait(200);
					} catch (InterruptedException e) {
						//do nothing.
					}
				}
				// If it's still alive after 3s send a signal to it
				// to see if it's still responding.
				if (l_pid == getPid(c_scanimgcmd))
				{
					// If it doesn't respond and it's still running kill the 
					// process and throw an error (which should cause us to 
					// try again)
					if (!isAlive(l_pid))
					{
						c_log.log(Level.WARNING, c_scanimgcmd + " did not die.");
						killPid(l_pid);
					}
					else
					{
						//Countdown, if it's still going after 12s, do something
						if (l_hang >= c_hangup) 
						{
							killPid(l_pid);
							break;
						}
						else 
						{
							l_hang += c_timeout;
						}
					}
				}
			} while (l_pid == getPid(c_scanimgcmd));
			
			// Java does not close these streams, so we need to do that here
			// to prevent too many open files error
			closeProcess(l_p);
		}
		
		//try to read in the images
		BufferedImage l_imgs[] = new BufferedImage[2];
		for (int l_i = 0; l_i < 2; l_i++)
		{
			try
			{
				File l_imgFile = new File(c_inpath + String.format(c_scanfmt, l_i+1));
				if (l_imgFile.exists())
				{
					try
					{
						RenderedOp l_op = JAI.create("FileLoad", l_imgFile.getAbsolutePath());
						l_imgs[l_i] = l_op.createInstance().getAsBufferedImage();
					}
					catch (Exception l_e)
					{
						l_imgs[l_i] = null;
						c_log.log(Level.WARNING, "Read Error: " + l_e.getMessage());
						//Handle the error image by moving it
					}
					
					//Delete or move the scanned image after reading.
					try
					{
						if (l_imgs[l_i] == null)
						{
							FileUtils.copyFile(l_imgFile, 
									new File(c_outpath + "readerror-" + c_err 
											+ ".tiff"));
							c_err++;
						}
						if (c_delete)
						{
							FileUtils.forceDelete(l_imgFile);
							
						}
						else
						{
							FileUtils.copyFile(l_imgFile, new File(c_outpath));
							FileUtils.forceDelete(l_imgFile);
						}
					}
					catch (Exception l_e)
					{
						c_log.log(Level.WARNING, "Unable to move or delete the" 
										+ " ballot image file.. Changing the"
										+ " scanformat name.");
						c_suffix++;
						c_scanopts += "-" + c_suffix;
						c_scanfmt += "-" + c_suffix;
					}
				}
				else
				{
					l_imgs[l_i] = null;
					c_log.log(Level.FINE, "Could not read " + l_imgFile.getName());
					//IT does not exist, so we can't move it.
				}
				
			}
			catch (Exception l_e)
			{
				//Couldn't even open it...
				l_imgs[l_i] = null;
				c_log.log(Level.WARNING, "Error: " + l_e.getMessage());
			}
		}
		
		//If we failed, check the return value. Log it.
		if (l_imgs == null || (l_imgs[0] == null && l_imgs[1] == null))
		{
			int l_err = l_p.exitValue();
			switch (l_err)
			{
				case 0:
				case 7: //This is the "out of documents" error.
					break;
				default:
					c_log.log(Level.WARNING, "Scanner exited with error code "
							+ l_err + "\n Message: " + getErrorMsg(l_p));
					break;
			}
		}

		return l_imgs;
	}

	/**
	 * Kill a process based on the PID.
	 * 
	 * @param p_pid
	 */
	private void killPid(int p_pid) {
		Process l_process = null; 
		
		try
		{
			synchronized (this) 
			{
				l_process = Runtime.getRuntime().exec(String.format(c_killcmd, p_pid)); 
				l_process.wait(); 
			}
		}
		catch(Exception l_e)
		{
			//Nothing.
		}
		finally {
			closeProcess(l_process); 
		}
	}

	private void closeProcess(Process p_process) {
		try {
			if(p_process != null) {
				p_process.getErrorStream().close();
				p_process.getInputStream().close(); 
				p_process.getOutputStream().close(); 
			}
		} catch (Exception e) {
			//do nothing
		}		
	}

	/**
	 * Determine if a process is alive based on the PID number.
	 * 
	 * @param p_pid
	 * @return
	 */
	private boolean isAlive(int p_pid) 
	{
		Process l_p;
		try
		{
			synchronized (this) 
			{
				l_p = Runtime.getRuntime().exec(String.format(c_sigcmd, p_pid));
				l_p.waitFor();
				if (l_p.exitValue() == 0)
				{
					return true;
				}
			}
		}
		catch(Exception l_e)
		{
			//Nothing.
		}
		return false;
	}

	/**
	 * Returns the PID for the given command.
	 * 
	 * @param p_cmd
	 * @return
	 */
	private int getPid(String p_cmd) 
	{
		int l_pid = 0;
		BufferedReader l_buf;
		Process l_p = null;
		try
		{
			l_p = Runtime.getRuntime().exec(String.format(c_pgrep, p_cmd));
			synchronized (this) {
				l_p.waitFor();	
			}
			l_buf = new BufferedReader(new InputStreamReader(l_p.getInputStream()));
			String l_str = l_buf.readLine();
			if (l_str != null && l_str.length() > 0)
			{
				l_pid = Integer.parseInt(l_str);				
			}
		} 
		catch (Exception e_p)
		{
			//Do nothing.
			l_pid = 0;
		}
		finally 
		{
			closeProcess(l_p);
		}
		
		return l_pid;
	}

	/**
	 * @return the c_scanimgcmd
	 */
	public String getScanimgcmd() {
		return c_scanimgcmd;
	}

	/**
	 * @param cScanimgcmd the c_scanimgcmd to set
	 */
	public void setScanimgcmd(String p_scanimgcmd) {
		c_scanimgcmd = p_scanimgcmd;
	}

	/**
	 * @return the c_testopts
	 */
	public String getTestopts() {
		return c_testopts;
	}

	/**
	 * @param cTestopts the c_testopts to set
	 */
	public void setTestopts(String p_testopts) {
		c_testopts = p_testopts;
	}

	/**
	 * @return the c_scanopts
	 */
	public String getScanopts() {
		return c_scanopts;
	}

	/**
	 * @param cScanopts the c_scanopts to set
	 */
	public void setScanopts(String p_scanopts) {
		c_scanopts = p_scanopts;
	}

	/**
	 * @return the c_log
	 */
	public Logging getLog() {
		return c_log;
	}

	/**
	 * @param cLog the c_log to set
	 */
	public void setLog(Logging p_log) {
		c_log = p_log;
	}


	public void setScanfmt(String scanfmt) {
		c_scanfmt = scanfmt;
	}

	public String getScanfmt() {
		return c_scanfmt;
	}

	/**
	 * @return the sigcmd
	 */
	public String getSigcmd() {
		return c_sigcmd;
	}

	/**
	 * @param p_sigcmd the sigcmd to set
	 */
	public void setSigcmd(String p_sigcmd) {
		c_sigcmd = p_sigcmd;
	}

	/**
	 * @return the killcmd
	 */
	public String getKillcmd() {
		return c_killcmd;
	}

	/**
	 * @param p_killcmd the killcmd to set
	 */
	public void setKillcmd(String p_killcmd) {
		c_killcmd = p_killcmd;
	}

	/**
	 * @return the pgrep
	 */
	public String getPgrep() {
		return c_pgrep;
	}

	/**
	 * @param p_pgrep the pgrep to set
	 */
	public void setPgrep(String p_pgrep) {
		c_pgrep = p_pgrep;
	}

	/**
	 * @return the timeout
	 */
	public long getTimeout() {
		return c_timeout;
	}

	/**
	 * @param p_timeout the timeout to set
	 */
	public void setTimeout(long p_timeout) {
		c_timeout = p_timeout;
	}

	/**
	 * @return the hangup
	 */
	public long getHangup() {
		return c_hangup;
	}

	/**
	 * @param p_hangup the hangup to set
	 */
	public void setHangup(long p_hangup) {
		c_hangup = p_hangup;
	}

	/**
	 * @return the delete
	 */
	public boolean isDelete() {
		return c_delete;
	}

	/**
	 * @param p_delete the delete to set
	 */
	public void setDelete(boolean p_delete) {
		c_delete = p_delete;
	}

	/**
	 * @param inpath the inpath to set
	 */
	public void setInpath(String inpath) {
		c_inpath = inpath;
	}

	/**
	 * @return the inpath
	 */
	public String getInpath() {
		return c_inpath;
	}

	/**
	 * @param outpath the outpath to set
	 */
	public void setOutpath(String outpath) {
		c_outpath = outpath;
	}

	/**
	 * @return the outpath
	 */
	public String getOutpath() {
		return c_outpath;
	}

	/**
	 * Using the given process, grab the error stream and report the result.
	 * 
	 * @param p_p
	 * @return
	 * @throws IOException
	 */
	private String getErrorMsg(Process p_p) throws IOException
	{
		String l_errmsg = "";
		String l_tmp = "";
		BufferedReader l_buf;
		l_buf = new BufferedReader(new InputStreamReader(p_p.getErrorStream()));
		//Read until empty/null
		l_tmp = l_buf.readLine();
		while (l_tmp != null)
		{
			l_errmsg += "\n" + l_tmp;
			l_tmp = l_buf.readLine();
		}
		return l_errmsg;
	}	
}
