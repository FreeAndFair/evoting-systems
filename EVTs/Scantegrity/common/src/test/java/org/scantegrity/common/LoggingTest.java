package org.scantegrity.common;

import java.util.Vector;
import java.util.logging.Level;
import org.junit.Test;

public class LoggingTest {

	/**
	 * @param args
	 */
	@Test
	public void testLogging()
	{
		Vector<String> l_dir = new Vector<String>();
		l_dir.add("./");
		l_dir.add("./target");
		Logging l_log = new Logging(l_dir, 12345, Level.ALL);
		l_log.log(Level.CONFIG, "Testing the config level for the logger.");
		l_log.log(Level.ALL, "Test message for the logger.");
	}
}
