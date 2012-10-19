package org.scantegrity.sws.action;

import javax.servlet.http.HttpSession;

import net.sourceforge.stripes.action.ActionBean;
import net.sourceforge.stripes.action.ActionBeanContext;
import net.sourceforge.stripes.action.RedirectResolution;
import net.sourceforge.stripes.action.Resolution;

public class RestrictedActionBean implements ActionBean {
	
	protected ActionBeanContext c_ctx;
	public ActionBeanContext getContext() {
		// TODO Auto-generated method stub
		return c_ctx;
	}

	public void setContext(ActionBeanContext arg0) {
		// TODO Auto-generated method stub
		c_ctx = arg0;
	}
	
	public Resolution checkUser()
	{		
		HttpSession c_sess = getContext().getRequest().getSession(true);
		if( c_sess.getAttribute("username") == null )
		{
			c_sess.setAttribute("redir", c_ctx.getRequest().getRequestURL().toString());
			//c_sess.setAttribute("redir", c_ctx.getRequest().getRequestURL().toString().replace("http://","https://"));
			String l_url = "https://" + c_ctx.getRequest().getServerName() + ":" + c_ctx.getRequest().getServerPort() + c_ctx.getRequest().getContextPath() + "/login";
			//String l_url = "https://" + c_ctx.getRequest().getServerName() + c_ctx.getRequest().getContextPath() + "/login";
			return new RedirectResolution(l_url,false);
		}
		return null;
	}
	

}
