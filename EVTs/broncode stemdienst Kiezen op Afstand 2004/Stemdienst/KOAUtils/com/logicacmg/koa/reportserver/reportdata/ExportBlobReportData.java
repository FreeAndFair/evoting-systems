/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.reportserver.reportdata.ExportBlobReportData.java
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
/**
 * Reportdata to get a blob report from the Reports table in the database.
 * This report data is used for the Export reports for the data manager.
 * 
 * @author uiterlix
 */
public class ExportBlobReportData
	extends AbstractReportData
	implements ReportData
{
	/**
	 * @see ReportData#init()
	 */
	Connection conn = null;
	PreparedStatement stmt = null;
	ResultSet rst = null;
	InputStreamReader myReader = null;
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
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ExportBlobReportData.init] Get connection");
			conn = xDbKoa.getConnection();
			conn.setReadOnly(true);
			String query =
				"SELECT * FROM KOA01.REPORTS WHERE TYPE!='"
					+ ESBSessionEJBBean.REPORT_TYPE_ELECTION_RESULT
					+ "' AND TYPE!='"
					+ ESBSessionEJBBean.REPORT_TYPE_DECRYPTED_VOTES
					+ "' AND ID="
					+ id;
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ExportBlobReportData.init] Prepare statement");
			stmt = conn.prepareStatement(query);
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ExportBlobReportData.init] Execute query");
			rst = stmt.executeQuery();
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ExportBlobReportData.init] Getting result");
			if (rst.next())
			{
				myBlob = rst.getBinaryStream("REPORT");
				InputStreamReader myReader =
					new InputStreamReader(myBlob, "UTF8");
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
			String[] params = { "BlobReportData" };
			KOALogHelper.logErrorCode(
				"ExportBlobReportData",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOAException(ErrorConstants.REPORT_EXPORT_DEFAULT, sqle);
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
			throw new KOAException(ErrorConstants.REPORT_EXPORT_DEFAULT, e);
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
			try
			{
				if (myReader != null)
				{
					myReader.close();
				}
			}
			catch (Exception e)
			{
				KOALogHelper.logErrorCode(
					"ExportBlobReportData.close",
					ErrorConstants.ERR_BLOBREPORT_CLOSE,
					e);
			}
			try
			{
				if (myBlob != null)
				{
					myBlob.close();
				}
			}
			catch (Exception e)
			{
				KOALogHelper.logErrorCode(
					"ExportBlobReportData.close",
					ErrorConstants.ERR_BLOBREPORT_CLOSE,
					e);
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
			KOALogHelper.logErrorCode(
				"ExportBlobReportData.close",
				ErrorConstants.ERR_BLOBREPORT_CLOSE,
				e);
		}
	}
}