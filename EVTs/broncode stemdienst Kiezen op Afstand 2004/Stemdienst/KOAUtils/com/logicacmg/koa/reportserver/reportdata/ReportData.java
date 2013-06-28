/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.reportserver.reportdata.ReportData.java
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
import java.util.Vector;

import javax.xml.transform.stream.StreamSource;

import com.logica.eplatform.error.EPlatformException;
import com.logicacmg.koa.reportserver.reportdata.ReportDataContext;
/**
 * Reportdata interface that must be implemented by all ReportData
 * implementations.
 * 
 * @author KuijerM
 */
public interface ReportData
{
	public void init() throws EPlatformException;
	public StreamSource getStreamSource();
	public void setStreamSource(StreamSource source);
	public ReportDataContext getReportDataContext();
	public void setReportDataContext(ReportDataContext reportContext);
	public Vector getAuthorizedRoles();
	public void setAuthorizedRoles(Vector authorizedRoles);
	public void close();
}