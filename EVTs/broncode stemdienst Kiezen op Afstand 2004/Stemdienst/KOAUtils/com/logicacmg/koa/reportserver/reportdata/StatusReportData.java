/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.reportserver.reportdata.StatusReportData.java
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
  *  0.1		11-05-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.reportserver.reportdata;
import javax.xml.transform.stream.StreamSource;

import com.logicacmg.koa.reportserver.KOAStatusReportXMLDBReader;
import com.logicacmg.koa.reportserver.command.KOAReportCommand;
import com.logicacmg.koa.reportserver.reportdata.AbstractReportData;
import com.logicacmg.koa.reportserver.reportdata.ReportData;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * The report data class file for the Status report
 * in the KOA Application
 * 
 * @author KuijerM
 */
public class StatusReportData extends AbstractReportData implements ReportData
{
	KOAStatusReportXMLDBReader reader = null;
	StreamSource streamSource = null;
	String sCaller = null;
	/**
	 * initialize the report data
	 * 
	 */
	public void init() throws com.logica.eplatform.error.EPlatformException
	{
		/* set stream source */
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[StatusReportData.init] setting stream source");
		sCaller = reportDataContext.getParameter(KOAReportCommand.CALLER);
		reader = new KOAStatusReportXMLDBReader(sCaller);
		streamSource = new StreamSource(reader);
		setStreamSource(streamSource);
	}
	/**
	 * @see ReportData#close()
	 */
	public void close()
	{
		if (reader != null)
		{
			try
			{
				reader.close();
			}
			catch (Exception ioe)
			{
				KOALogHelper.log(
					KOALogHelper.WARNING,
					"[StatusReportData.close] Error closing db reader");
			}
		}
	}
}