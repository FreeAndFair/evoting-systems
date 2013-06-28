/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.services.KOASchedulerServlet.java
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
import com.logicacmg.koa.scheduler.Scheduler;
/** 
 * This servlet is loaded at AppServer startup and starts
 * a scheduling thread in the WebContainer.
 * 
 * @author KuijerM
 */
public class KOASchedulerServlet extends HttpServlet
{
	Scheduler scheduler = null;
	/**
	 * Initialized the Scheduler Servlet
	 * 
	 * @throws javax.servlet.ServletException
	 */
	public void init() throws javax.servlet.ServletException
	{
		scheduler = new Scheduler();
	}
	/**
	 * Destroy the Scheduler Servlet
	 */
	public void destroy()
	{
		super.destroy();
		scheduler.setRequiredStatus(false);
	}
	/** 
	 * This method reports the state of the scheduler.
	 * RESERVED for admins.
	 * 
	 * @param request		Object that encapsulates the request to the servlet
	 * @param response		Object that encapsulates the response from the servlet
	 * 
	 * @throws ServletException
	 * @throws IOException
	 */
	public void doGet(
		javax.servlet.http.HttpServletRequest request,
		javax.servlet.http.HttpServletResponse response)
		throws javax.servlet.ServletException, java.io.IOException
	{
		String action = request.getParameter("action");
		if (action != null)
		{
			if (action.equals("start"))
			{
				if (!scheduler.isRunning())
				{
					scheduler = new Scheduler();
				}
			}
			if (action.equals("stop"))
			{
				scheduler.setRequiredStatus(false);
			}
		}
		java.io.PrintWriter printer = response.getWriter();
		printer.write("<html><body><h1>scheduler</h1>");
		printer.write("Required status is " + scheduler.getRequiredStatus());
		printer.write("</body></html>");
	}
}
