package com.logicacmg.koa.logging;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;

import com.logica.eplatform.services.ServiceContext;
import com.logica.eplatform.services.logging.LogServiceImpl;
/**
 * New log service implementation, which reuses
 * printwriter. Is about 10x better for performance.
 * 
 * @author KvdPloeg
 */
public class FastLogServiceImpl extends LogServiceImpl
{
	protected PrintWriter out = null;
	/** 
	 * Constructor
	 */
	public FastLogServiceImpl() throws java.rmi.RemoteException
	{
	}
	/**
	 * Initializes the logging system.
	 * Initialized the printwriter based on the file
	 * supplied in the service context under key 'filename'
	 */
	public void init() throws java.rmi.RemoteException
	{
		ServiceContext sc = getServiceContext();
		String fileName = sc.getProperty("filename");
		try
		{
			out = new PrintWriter(new FileWriter(fileName, true), true);
			System.out.println(
				sc.getServiceName()
					+ " initialized at "
					+ new java.util.Date());
			log(
				sc.getServiceName()
					+ " initialized at "
					+ new java.util.Date());
		}
		catch (IOException ioe)
		{
			System.err.println(ioe.getMessage());
		}
	}
	/**
	 * Writes a line to the log file (printwriter).
	 * 
	 * @param msg the message to log
	 */
	public synchronized void log(String msg) throws java.rmi.RemoteException
	{
		if (out != null)
			out.println("[" + new java.util.Date() + "] " + msg);
	}
	/**
	 * Cleanup the resources we're using, printwriters.
	 */
	protected void finalize()
	{
		try
		{
			//close printwriter
			out.close();
		}
		catch (Exception e)
		{
			System.err.println(e.getMessage());
		}
	}
}