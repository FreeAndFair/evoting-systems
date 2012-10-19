/*
 * @(#)DAOFactory.java
 *  
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
package org.scantegrity.sws.action;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.SQLException;
import java.util.Properties;
import java.util.ResourceBundle;

/**
 * Connect once to the database, then make sure it's still open each time.
 * we need to use it.
 * 
 * @author carback1
 * @version 0.0.1
 * @date Oct 25, 2011
 **/

public final class DAOFactory {
	
    private static final DAOFactory INSTANCE = new DAOFactory();

	private static Connection c_dbConn;
	private static String c_connStr;
	//default Parameters for database connection
	private static final String c_dbAddress = "jdbc:derby:";
	private static final String c_dbName = "TPDB";
	private static final String c_dbUser = "APP";
	private static final String c_dbPass = "";
	
    private DAOFactory()
    {
        if (INSTANCE != null) {
            throw new IllegalStateException("Already instantiated");
        }
        ResourceBundle l_bundle = ResourceBundle.getBundle("Database");
		// Use the default settings if the properties file is unavailable.
		String l_drv = (l_bundle.containsKey("DatabaseDriver")) 
						? l_bundle.getString("DatabaseDriver") : c_dbAddress;
		String l_dbName = (l_bundle.containsKey("DatabaseName")) 
							? l_bundle.getString("DatabaseName") : c_dbName;
		String l_userName = (l_bundle.containsKey("DatabaseUser")) 
							? l_bundle.getString("DatabaseUser") : c_dbUser;
		String l_userPass = (l_bundle.containsKey("DatabasePW")) 
							? l_bundle.getString("DatabasePW") : c_dbPass;
							
		c_connStr = l_drv + l_dbName +  ";create=true"
						+ ";user=" + l_userName
						+ ";password=" + l_userPass;
		try {
			Connect();
		} catch (Exception e) {
			System.err.println(e.getMessage());
			e.printStackTrace();
		}
		System.out.println("DAO (Database Access Object) Initialized.");
    }
    
    public static DAOFactory getInstance()
    {
    	return INSTANCE;
    }
    
    
    /**
     * Connects to the database. 
     * 
     * @throws InstantiationException
     * @throws IllegalAccessException
     * @throws ClassNotFoundException
     * @throws SQLException
     */
	private static void Connect() 
	throws InstantiationException, IllegalAccessException, 
			ClassNotFoundException, SQLException
	{
		//Load derby database driver
		Class.forName("org.apache.derby.jdbc.EmbeddedDriver").newInstance();
//		Properties prop = System.getProperties();
//		System.out.println("java.class.path now = "  
//							+ prop.getProperty("java.class.path", null));
//		System.out.println("LibPath: " + "Library path: '" 
//							+ System.getProperty( "java.library.path" ));
//		//System.err.println("Connect String: " + c_connStr);
		c_dbConn = DriverManager.getConnection(c_connStr);
	}
		
	/**
	 * Verifies if the connection is alive. If not, tries to reconnect, then
	 * if it fails again, throws an SQLEXception indicating the database is 
	 * broken.
	 * 
	 * @return
	 * @throws SQLException
	 * @throws ClassNotFoundException 
	 * @throws IllegalAccessException 
	 * @throws InstantiationException 
	 */
    public Connection getConnection() 
    throws SQLException, InstantiationException, 
    		IllegalAccessException, ClassNotFoundException
    {
    	if (c_dbConn == null || !c_dbConn.isValid(5))
    	{
    		Connect();
    		if (!c_dbConn.isValid(5))
    		{
    			throw new SQLException("Unable to connect to database.");
    		}
    	}
    	return c_dbConn;
    }
    
    protected void finalize()
    {
    	try {
			c_dbConn.close();
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
    }
    
}
