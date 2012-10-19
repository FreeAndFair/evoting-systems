package org.scantegrity.common; 

import java.io.File;
import java.util.Vector;
import java.util.logging.FileHandler;
import java.util.logging.Level;
import java.util.logging.LogRecord;
import java.util.logging.Logger;
import java.util.logging.XMLFormatter;

/**
 * This class is a wrapper of java.util.logging.Logger that
 * is customized for Scantegrity. The log methods have been overridden 
 * to provide for time and sequence information to always 
 * be set to 0 when the log is written to in order to preserve
 * anonymity. When using this class, only use the log methods 
 * that take LogRecord, or level, msg. The 
 * logp methods and the rest of the log methods have not been overridden.
 * 
 * @author jconway
 *
 */
public class Logging
{
	private Logger c_log = null;
	private XMLFormatter c_formatter; 
	private static String c_fname = "scanner-log-%d.txt";
	
	/**
	 * Constructor for all logging classes.
	 * 
	 * Defines a global logger, called "org.scantegrity.loggger"
	 * 
	 * Adds a logfile to each directory path sent to it.
	 * 
	 * @param p_logDirs
	 * @param p_id
	 * @param p_level
	 */
	public Logging(Vector<String> p_logDirs, int p_id, Level p_level)
	{
		c_log = Logger.getLogger("org.scantegrity.logger");
		c_formatter = new XMLFormatter(); 
		FileHandler l_handler = null;
		for (String l_dir : p_logDirs)
		{
			File l_d = new File(l_dir);
			if (!(l_d.isDirectory())) continue;
			try {
				l_handler = new FileHandler(l_d.getAbsolutePath() + File.separator
									+ String.format(c_fname, p_id));
			} catch (Exception l_e) {
				l_e.printStackTrace();
			}
			l_handler.setFormatter(c_formatter);
			c_log.addHandler(l_handler);
		}
		c_log.setLevel(p_level);
	}
	
	/**
	 * Log a record.
	 * 
	 * @param p_record
	 */
	public void log(LogRecord p_record)
	{
		p_record.setMillis(0);
		p_record.setSequenceNumber(0);
		c_log.log(p_record);
	}

	/**
	 * Writes the log to the logger
	 * @param p_level
	 * @param p_message
	 */
	public void log(Level p_level, String p_message)
	{
		LogRecord l_record = new LogRecord(p_level, p_message);
		this.log(l_record);
	} 
}