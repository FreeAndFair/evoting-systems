/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.db.LoggingDB.java
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
import java.sql.SQLException;
import java.sql.Timestamp;
import java.util.Date;

import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.db.DBUtils;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Class containing all the database actions for the logging
 * 
 * @author KuijerM
 */
public class LoggingDB
{
	private static String INSERT_AUDIT =
		"INSERT INTO KOA01.AUDIT_LOG "
			+ " (TIMESTAMP, TYPE, ACTION, COMPONENT, INITIATOR, MESSAGE) "
			+ "VALUES (?, ?, ?, ?, ?, ?);";
	private static String INSERT_ERROR =
		"INSERT INTO KOA01.ERROR_LOG "
			+ " (TIMESTAMP, COMPONENT, MESSAGE, DETAILS) "
			+ "VALUES (?, ?, ?, ?);";
	/**
	 * Insert an audit message in the database
	 * 
	 * @param iType int Int representation of the type
	 * @param sComponent The component in which the message is logged
	 * @param sMessage The message to log
	 * 
	 * @throws KOAException if something goes wrong during insertion of the audit message
	 * 
	 */
	public void insertAuditRecord(
		int iType,
		String sAction,
		String sComponent,
		String sMessage)
		throws KOAException
	{
		this.insertAuditRecord(iType, sAction, sComponent, null, sMessage);
	}
	/**
	 * Insert an audit message in the database
	 * 
	 * @param iType int Int representation of the type
	 * @param sAction The action that started the logging
	 * @param sComponent The component in which the message is logged
	 * @param sActor The initiator of the logging (person)
	 * @param sMessage The message to log
	 * 
	 * @throws KOAException if something goes wrong during insertion of the audit message
	 */
	public void insertAuditRecord(
		int iType,
		String sAction,
		String sComponent,
		String sActor,
		String sMessage)
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[LoggingDB.insertAuditRecord] start inserting audit record in database");
		String sType = KOALogHelper.getTypeForInt(iType);
		if (sAction == null)
		{
			sAction = "Unknown";
		}
		if (sMessage == null)
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[LoggingDB.insertAuditRecord] Could not log record, no message to log");
			throw new KOAException(ErrorConstants.AUDIT_LOG_INSERT);
		}
		/* init the DBUtils class */
		DBUtils xDBUtils =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
		/* execute the query */
		Connection conn = null;
		PreparedStatement xPre = null;
		try
		{
			/* get the connection */
			conn = xDBUtils.getConnection();
			Timestamp tsTimestamp = new Timestamp(new Date().getTime());
			/* setup the prepared statement */
			xPre = conn.prepareStatement(INSERT_AUDIT);
			xPre.setTimestamp(1, tsTimestamp);
			xPre.setString(2, sType);
			xPre.setString(3, sAction);
			xPre.setString(4, sComponent);
			xPre.setString(5, sActor);
			xPre.setString(6, sMessage);
			/* execute the statement */
			xPre.executeUpdate();
		}
		/* catch all the errors concerning SQL */
		catch (SQLException sqle)
		{
			KOALogHelper.logErrorCode(
				"LoggingDB.insertAuditRecord",
				ErrorConstants.ERR_AUDIT_INSERT,
				sqle);
			throw new KOAException(ErrorConstants.AUDIT_LOG_INSERT, sqle);
		}
		finally
		{
			/* close everything */
			xDBUtils.closePreparedStatement(xPre);
			xDBUtils.closeConnection(conn);
		}
	}
}