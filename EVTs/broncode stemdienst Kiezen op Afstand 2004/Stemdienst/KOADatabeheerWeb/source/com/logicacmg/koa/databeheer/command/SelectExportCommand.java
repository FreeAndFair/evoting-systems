/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.databeheer.command.SelectExportCommand.java
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
  *  1.0		14-05-2003	XUi		First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.databeheer.command;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Timestamp;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.Vector;

import com.logica.eplatform.error.EPlatformException;
import com.logica.eplatform.util.LogHelper;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.databeheer.command.CommandConstants;
import com.logicacmg.koa.databeheer.dataobjects.ExportItem;
import com.logicacmg.koa.db.DBUtils;
import com.logicacmg.koa.esb.beans.ESBSessionEJBBean;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * SelectExportCommand. 
 * Used for the 'databeheerder' to select an export he/she wants to save.
 * 
 * @author: XUi
 */
public class SelectExportCommand
	extends com.logica.eplatform.command.AbstractTargetableCommand
	implements com.logica.eplatform.command.http.HttpCommand
{
	private java.lang.String RESULT_JSP;
	private boolean logout = false;
	private Vector exportItems = null;
	/**
	 * The execute method on the SelectExport command.
	 * This method is executed in the ejb command target.
	 * For the LoginCommand the execute method doesn't do anything.
	 */
	public void execute()
		throws com.logica.eplatform.command.CommandException, EPlatformException
	{
		KOALogHelper.log(LogHelper.INFO, "[SelectExportCommand] execute");
		/* Get datasource */
		DBUtils xDbKoa =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
		SimpleDateFormat xFormat = new SimpleDateFormat("dd.MM.yyyy HH:mm");
		Connection conn = null;
		PreparedStatement stmt = null;
		ResultSet rst = null;
		try
		{
			conn = xDbKoa.getConnection();
			conn.setReadOnly(true);
			String query =
				"SELECT ID, TYPE, TIMESTAMP FROM KOA01.REPORTS WHERE TYPE!='"
					+ ESBSessionEJBBean.REPORT_TYPE_ELECTION_RESULT
					+ "' AND TYPE!='"
					+ ESBSessionEJBBean.REPORT_TYPE_DECRYPTED_VOTES
					+ "' ORDER BY ID DESC";
			stmt = conn.prepareStatement(query);
			rst = stmt.executeQuery(query);
			int vectCount = 0;
			while (rst.next())
			{
				Timestamp tStamp = rst.getTimestamp("TIMESTAMP");
				Date date = new Date(tStamp.getTime());
				ExportItem item =
					new ExportItem(
						rst.getInt("ID"),
						rst.getString("TYPE"),
						date);
				// KOALogHelper.log(KOALogHelper.INFO, "[SelectExportCommand] Adding exportitem: " + item.getId() + "," + item.getType() + "," + item.getDate());
				exportItems.add(vectCount, item);
				vectCount++;
			}
		}
		catch (SQLException sqle)
		{
			String[] params = { "Select all reports not election result" };
			KOALogHelper.logErrorCode(
				"[SelectExportCommand.execute]",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
		}
		finally
		{
			xDbKoa.closeResultSet(rst);
			xDbKoa.closePreparedStatement(stmt);
			xDbKoa.closeConnection(conn);
			conn = null;
		}
		/* Put results in ExportItem objects */
	}
	/**
	 * Return the JSP to display errors.
	 * Creation date: (20-2-2001 14:24:17)
	 * @return String The error JSP
	 */
	public String getErrorJSP()
	{
		return CommandConstants.DEFAULT_ERROR_JSP;
	}
	/**
	 * Return the JSP page to display the result.
	 * Creation date: (20-2-2001 14:24:17)
	 * @return String The result JSP
	 */
	public String getResultJSP()
	{
		return RESULT_JSP;
	}
	/**
	 * Initialises the command. In the init the parameters can be
	 * extracted from the request.
	 * Creation date: (07-04-2003 14:24:17)
	 * @param request The current request
	 */
	public void init(HttpServletRequest request) throws EPlatformException
	{
		LogHelper.trace(LogHelper.TRACE, "[SelectExportCommand] init");
		exportItems = new Vector();
		RESULT_JSP = "selectexport.jsp";
	}
	/**
	 * Update the current session.
	 * Creation date: (07-04-2003 13:35:21)
	 * @param session the session to update
	 */
	public void updateSession(javax.servlet.http.HttpSession session)
	{
	}
	/**
	 * Gets the exportItems
	 * @return Returns a Vector
	 */
	public Vector getExportItems()
	{
		return exportItems;
	}
}
