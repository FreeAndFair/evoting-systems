/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.reportserver.reportdata.VerkiezingsUitslagReportData.java
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
  *  0.1		11-05-2003	XUi			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.reportserver.reportdata;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;

import javax.xml.transform.stream.StreamSource;

import com.logica.eplatform.error.EPlatformException;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.db.DBUtils;
import com.logicacmg.koa.esb.beans.ESBSessionEJBBean;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.reportserver.reportdata.AbstractReportData;
import com.logicacmg.koa.reportserver.reportdata.ReportData;
import com.logicacmg.koa.utils.KOALogHelper;
public class VerkiezingsUitslagReportData
	extends AbstractReportData
	implements ReportData
{
	/**
	 * @see ReportData#init()
	 */
	Connection conn = null;
	PreparedStatement stmt = null;
	ResultSet rst = null;
	InputStream myBlob = null;
	DBUtils xDbKoa = null;
	public void init() throws EPlatformException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ExportBlobReportData.init] Initializing ReportData");
		String id = reportDataContext.getParameter("id");
		try
		{
			xDbKoa =
				new DBUtils(
					JNDIProperties.getProperty(
						JNDIProperties.DATASOURCE_KOA_NO_TRANS));
			conn = xDbKoa.getConnection();
			conn.setReadOnly(true);
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ExportBlobReportData.init] Check for verkiezingsuitslag");
			/* First make sure there's only 1 verkiezingsuitslag */
			String query =
				"SELECT COUNT(ID) AS AANTAL FROM KOA01.REPORTS WHERE TYPE='"
					+ ESBSessionEJBBean.REPORT_TYPE_ELECTION_RESULT
					+ "'";
			stmt = conn.prepareStatement(query);
			rst = stmt.executeQuery();
			if (rst.next())
			{
				// An uitslag has been found!
				if (!rst.getString("AANTAL").equals("1"))
				{
					KOALogHelper.log(
						KOALogHelper.TRACE,
						"[ExportBlobReportData.init] Geen of meer dan 1 verkiezingsuitslag gevonden.");
					throw new KOAException(
						ErrorConstants
							.REPORT_VERKIEZINGSUITSLAG_MEER_UITSLAGEN);
				}
			}
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ExportBlobReportData.init] Get uitslag");
			query =
				"SELECT * FROM KOA01.REPORTS WHERE TYPE='"
					+ ESBSessionEJBBean.REPORT_TYPE_ELECTION_RESULT
					+ "'";
			stmt = conn.prepareStatement(query);
			rst = stmt.executeQuery();
			if (rst.next())
			{
				myBlob = rst.getBinaryStream("REPORT");
				InputStreamReader myReader = new InputStreamReader(myBlob);
				setStreamSource(new StreamSource(myReader));
			}
			else
			{
				/* No records found */
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[ExportBlobReportData.init] No records found!");
				close();
			}
		}
		catch (SQLException sqle)
		{
			close();
			String[] params = { "Verkiezingsuitslag" };
			KOALogHelper.logErrorCode(
				"ExportBlobReportData",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOAException(
				ErrorConstants.REPORT_VERKIEZINGSUITSLAG_DEFAULT,
				sqle);
		}
		catch (KOAException koae)
		{
			close();
			KOALogHelper.logError(
				"ExportBlobReportData",
				"KOAException, are the JNDI properties valid?",
				koae);
			throw koae;
		}
		catch (Exception e)
		{
			close();
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ExportBlobReportData.init] Unknown error!");
			throw new KOAException(
				ErrorConstants.REPORT_VERKIEZINGSUITSLAG_DEFAULT,
				e);
		}
	}
	/**
	 * @see ReportData#close()
	 */
	public void close()
	{
		try
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ExportBlobReportData.close] Closing ReportData.");
			if (myBlob != null)
			{
				myBlob.close();
			}
			xDbKoa.closeResultSet(rst);
			xDbKoa.closePreparedStatement(stmt);
			xDbKoa.closeConnection(conn);
			conn = null;
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ExportBlobReportData.close] Closed ReportData.");
		}
		catch (Exception e)
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ExportBlobReportData.close] Unknown error!");
		}
	}
}