/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.services.KOAServiceRackServlet.java
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
  *  0.1		23-04-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.servlet;
import javax.naming.NamingException;

import com.logica.eplatform.services.ServicesRack;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Servlet for all services
 */
public class KOAServicesRackServlet extends HttpServlet
{
	ServicesRack rack = null;
	/**
	 * Init the servlet
	 * init all services.
	 * 
	 * @throws ServletException	when something goes wrong with the initialization
	 */
	public void init() throws ServletException
	{
		/* create a new services rack to start all the service */
		rack = new ServicesRack(false);
	}
	/**
	 * Destroy the servlet and stop all services
	 */
	public void destroy()
	{
		/* destroy the servlet */
		super.destroy();
		try
		{
			/* when the servlet is destroyed, unbind the services rack */
			rack.unbindServices();
		}
		catch (NamingException ne)
		{
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[KOAServicesRackServlet.destroy] Could not unbind survices ");
		}
	}
}