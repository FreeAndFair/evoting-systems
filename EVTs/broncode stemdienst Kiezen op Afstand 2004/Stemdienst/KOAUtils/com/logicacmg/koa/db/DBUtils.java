/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.db.DBUtils.java
  *
  * -----------------------------------------------------------------------
  * 
  *  (c) 2003  Ministerie van Binnenlandse Zaken en Koninkrijkrelaties
  *
  *  Project		: Kiezen Op Afstand (KOA)
  *  Project Number	: ECF-2651
  *  
  *  History:
  *  Version	Date		Name		Reason
  * ---------------------------------------------------------
  *  0.1		14-04-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.db;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.Hashtable;

import javax.naming.Context;
import javax.naming.InitialContext;
import javax.naming.NamingException;
import javax.sql.DataSource;

import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.exception.KOADBException;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
import com.logicacmg.koa.utils.ObjectCache;
/**
 * Helper class for non-entitybean DB interactions 
 * 
 * @author KuijerM
 * 
 */
public class DBUtils
{
	/**
	 * The URL provider for the initialContext
	 * 
	 */
	private String g_sProviderURL = null;
	/**
	 * The Data Source JNDI name
	 * 
	 */
	private String g_sDataSourceName = null;
	/**
	 * The instance of the datab
	 * 
	 */
	private DataSource g_dsDataSource = null;
	/**
	 * Constructor that takes the url provider and datasource name
	 * 
	 * @param sProviderURL The Provider url
	 * @param sDataSourceName The name of the datasource.
	 * 
	 */
	public DBUtils(String sDataSourceName)
	{
		/* setting parameters */
		this.setDataSourceName(sDataSourceName);
	}
	/**
	 * Set the datasource name
	 * 
	 * @param sDataSourceName The datasource name
	 * 
	 */
	public void setDataSourceName(String sDataSourceName)
	{
		/* set datasourcename */
		g_sDataSourceName = sDataSourceName;
		/* try to get the datasource from the object cache */
		g_dsDataSource =
			ObjectCache.getInstance().getDataSource(sDataSourceName);
		/* if we failed to get one, init a new one */
		if (g_dsDataSource == null)
		{
			try
			{
				/* get the initial context based on the url provider */
				InitialContext icContext = this.getInitialContext();
				/* lookup the datasource form the initial context */
				g_dsDataSource =
					(DataSource) icContext.lookup(g_sDataSourceName);
				/* put the datasource in the cache */
				ObjectCache.getInstance().putDataSource(
					sDataSourceName,
					g_dsDataSource);
			}
			catch (NamingException ne)
			{
				String[] params = { "Datasource " + g_sDataSourceName };
				KOALogHelper.logErrorCode(
					"DBUtils.getConnection",
					ErrorConstants.ERR_NAMING,
					params,
					ne);
			}
			catch (KOAException koae)
			{
				KOALogHelper.logError(
					"DBUtils.getConnection",
					"KOAException getting initial context",
					koae);
			}
		}
	}
	/**
	 * Executes a query that has a result set
	 * Note: statement, recordset and connection are not closed.
	 * 
	 * @param sQuery The query to execute
	 * 
	 * @return ResultSet The result of the query
	 * 
	 */
	public ResultSet executeResultQuery(Statement stmtStatement, String sQuery)
		throws KOADBException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[DBUtils.executeResultQuery] start executing query : " + sQuery);
		ResultSet rsResult = null;
		try
		{
			/* execute the query with the result */
			rsResult = stmtStatement.executeQuery(sQuery);
		}
		catch (SQLException sqle)
		{
			String[] params = { "error in executing query : " + sQuery };
			KOALogHelper.logErrorCode(
				"DBUtils.executeResultQuery",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOADBException(ErrorConstants.DBUTILS_EXEC_QUERY, sqle);
		}
		return rsResult;
	}
	/**
	 * Executes a query without a result
	 * 
	 * @param sQuery The query to execute
	 * 
	 * @return A integer indicating the number of records affected.
	 * 
	 * 
	 */
	public int executeQuery(String sQuery) throws KOADBException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[DBUtils.executeQuery] start executing query : " + sQuery);
		int iResult = 0;
		Connection conn = null;
		Statement stmtStatement = null;
		try
		{
			/* get the connection to the datasource */
			conn = this.getConnection();
			/* create the statement from the connection */
			stmtStatement = conn.createStatement();
			/* execute the query */
			iResult = stmtStatement.executeUpdate(sQuery);
		}
		catch (SQLException sqle)
		{
			String[] params = { "error in executing query : " + sQuery };
			KOALogHelper.logErrorCode(
				"DBUtils.executeQuery",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOADBException(ErrorConstants.DBUTILS_EXEC_QUERY, sqle);
		}
		/* always close the connection and statement */
		finally
		{
			this.closeStatement(stmtStatement);
			this.closeConnection(conn);
		}
		return iResult;
	}
	/**
	 * The connection to the datasource
	 * 
	 * @return Connection The connection to the datasource
	 * 
	 * @throws KOADBException exception when something goes wrong getting connection
	 * 
	 */
	public Connection getConnection() throws KOADBException
	{
		InitialContext icContext = null;
		Connection conn = null;
		/* if the datasource is not specified, throw new KOA DB exception */
		if (g_dsDataSource == null)
		{
			KOALogHelper.logError(
				"DBUtils.getConnection",
				"Datasource name not specified",
				null);
			throw new KOADBException(ErrorConstants.DBUTILS_NO_DATASOURCE);
		}
		try
		{
			/* create the connection from the datasource */
			conn = g_dsDataSource.getConnection();
		}
		catch (SQLException sqle)
		{
			String[] params =
				{ "Getting connection from datasource " + g_dsDataSource };
			KOALogHelper.logErrorCode(
				"DBUtils.getConnection",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOADBException(
				ErrorConstants.DBUTILS_GET_CONNECTION,
				sqle);
		}
		return conn;
	}
	/**
	 * Close the specified result set
	 * 
	 * @param rsSet The resultset to close
	 * 
	 */
	public void closeResultSet(ResultSet rsSet)
	{
		try
		{
			/* try to close the result set */
			if (rsSet != null)
			{
				rsSet.close();
			}
		}
		/* log a warning if something goes wrong */
		catch (SQLException sqle)
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[DBUtils.closeRecordSet] Could not close result set");
		}
	}
	/**
	 * Close the specified statement
	 * 
	 * @param stmtStatement the statement to close
	 * 
	 */
	public void closeStatement(Statement stmtStatement)
	{
		try
		{
			/* try to close the statement */
			if (stmtStatement != null)
			{
				stmtStatement.close();
			}
		}
		catch (SQLException sqle)
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[DBUtils.closeStatement] Could not close statement");
		}
	}
	/**
	 * Close the specified prepared statement
	 * 
	 * @param stmtStatement the prepared statement to close
	 * 
	 */
	public void closePreparedStatement(PreparedStatement stmtStatement)
	{
		try
		{
			/* try to close the prepared statement */
			if (stmtStatement != null)
			{
				stmtStatement.close();
			}
		}
		/* log a warning if something goes wrong */
		catch (SQLException sqle)
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[DBUtils.closePreparedStatement] Could not close prepared statement");
		}
	}
	/**
	 * Close the specified connection
	 * 
	 * @param conn the connection to close
	 * 
	 */
	public void closeConnection(Connection conn)
	{
		try
		{
			/* try to close the connection */
			if (conn != null)
			{
				conn.close();
			}
		}
		/* log a warning if something goes wrong */
		catch (SQLException sqle)
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[DBUtils.closeConnection] Could not close connection");
		}
	}
	/**
	 * get the initialcontext to the datasource
	 * 
	 * @return InitialContext The context to search for the datasource
	 * 
	 * @throws NamingException an exception when naming is not found
	 * @throws KOAException Exception when the jndi properties are not found
	 * 
	 */
	private InitialContext getInitialContext()
		throws NamingException, KOAException
	{
		/* hashtable to put the properties in */
		Hashtable htProps = new Hashtable();
		/* put the parameters in the hashtable */
		htProps.put(
			Context.INITIAL_CONTEXT_FACTORY,
			JNDIProperties.getProperty(
				JNDIProperties.DATASOURCE_CONTEXT_FACTORY));
		htProps.put(
			Context.PROVIDER_URL,
			JNDIProperties.getProperty(JNDIProperties.DATASOURCE_PROVIDER));
		/* create new initial context based on the properties */
		InitialContext icContext = new InitialContext(htProps);
		return icContext;
	}
}