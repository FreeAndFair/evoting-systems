/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.reportserver.command.ReportCommand.java
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
  *  0.1		12-05-2003	XUi			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.reportserver.command;
import com.logicacmg.koa.reportserver.report.Report;
import com.logicacmg.koa.reportserver.reportdata.ReportData;
public interface ReportCommand
{
	/**
	 * Returns the Report of a command.
	 */
	Report getReport();
	/**
	 * returns the ReportData of the command.
	 */
	ReportData getReportData();
}