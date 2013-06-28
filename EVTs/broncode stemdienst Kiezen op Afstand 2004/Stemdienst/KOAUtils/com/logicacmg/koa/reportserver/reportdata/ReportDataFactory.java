/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.reportserver.reportdata.ReportDataFactory.java
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
  *  0.1		09-05-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.reportserver.reportdata;
import java.io.IOException;
import java.util.Properties;
import java.util.StringTokenizer;
import java.util.Vector;

import com.logica.eplatform.util.LogHelper;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.reportserver.reportdata.ReportData;
import com.logicacmg.koa.reportserver.reportdata.ReportDataContext;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Factory to get the report data implementation based on the reportdata name.
 * 
 * @author KuijerM
 * 
 */
public class ReportDataFactory
{
	// Singleton...
	static private ReportDataFactory instance = null;
	// Globals
	private Properties globalProperties = new Properties();
	private ReportDataFactory()
	{
	}
	/**
	 * @return ReportData based on a name
	 */
	public ReportData getReportData(String name) throws Exception
	{
		LogHelper.trace(LogHelper.TRACE, "[ReportDataFactory] getReportData");
		return this.getReportData(name, new Properties());
	}
	/**
	 *	@param name			The name of the reportdata to get
	 *	@param parameters	Any properties needed for the report data
	 *
	 *  @return ReportData 
	 */
	public ReportData getReportData(String name, Properties parameters)
		throws KOAException
	{
		try
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ReportDataFactory] getReportData");
			ReportData reportData =
				(ReportData) Class
					.forName(globalProperties.getProperty(name + ".class"))
					.newInstance();
			String authorizedRoles =
				globalProperties.getProperty(name + ".roles");
			Vector vRoles = new Vector();
			StringTokenizer token = new StringTokenizer(authorizedRoles, ",");
			String role;
			while (token.hasMoreTokens())
			{
				role = token.nextToken();
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[ReportData.getReportData] Adding authorized role: "
						+ role);
				vRoles.add(role);
			}
			reportData.setAuthorizedRoles(vRoles);
			reportData.setReportDataContext(
				new ReportDataContext(name, globalProperties, parameters));
			return reportData;
		}
		catch (Exception e)
		{
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[ReportDataFactory] "
					+ e.getClass().getName()
					+ " in getReportData: "
					+ e.getMessage());
			throw new KOAException(
				ErrorConstants.REPORTDATA_GET_REPORTDATA,
				new String[] { name },
				e);
		}
	}
	/**
	 *  Returns the instance of the ReportDataFactory.
	 * 
	 * @return ReportDataFactory
	 * 
	 * @throws KOAException when the reportdata properties can not be read
	 */
	public static ReportDataFactory getReportDataFactory() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ReportDataFactory] getReportDataFactory");
		if (instance == null)
		{
			instance = new ReportDataFactory();
			try
			{
				instance.init();
			}
			catch (Exception e)
			{
				KOALogHelper.log(
					KOALogHelper.INFO,
					"[ReportDataFactory] "
						+ e.getClass().getName()
						+ " in getReportDataFactory");
				throw new KOAException(ErrorConstants.REPORTDATA_INIT, e);
			}
		}
		return instance;
	}
	/**
	 * Initializes the ReportDataFactory
	 * 
	 * @throws KOAException when the reportdata properties can not be read 
	 */
	private void init() throws KOAException
	{
		try
		{
			globalProperties.load(
				this.getClass().getResourceAsStream("/reportdata.properties"));
		}
		catch (IOException ioe)
		{
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[ReportDataFactory] init IOException " + ioe.getMessage());
			throw new KOAException(ErrorConstants.REPORTDATA_INIT, ioe);
		}
	}
}