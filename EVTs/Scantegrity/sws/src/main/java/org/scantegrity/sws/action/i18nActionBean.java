package org.scantegrity.sws.action;

import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpSession;

import net.sourceforge.stripes.action.ActionBean;
import net.sourceforge.stripes.action.ActionBeanContext;
import net.sourceforge.stripes.action.DefaultHandler;
import net.sourceforge.stripes.action.ForwardResolution;
import net.sourceforge.stripes.action.Resolution;

public class i18nActionBean implements ActionBean{
    private static final String VIEW = "/WEB-INF/jsp/i18n.jsp";
	
    private String c_name;
    public String getName() {
        return c_name;
    }
    private String c_locale;
    public String getLocale() {
        return c_locale;
    }
    

    @DefaultHandler
    public Resolution submit() {
    	HttpServletRequest l_request = c_ctx.getRequest();
    	HttpSession l_session = l_request.getSession();
    	c_name = l_request.getParameter("name");
    	if (c_name == null) {
        	c_name = (String) l_session.getAttribute("name");
        	if (c_name == null) {
        		c_name = (String)l_request.getHeader("User-Agent");
        	}
    	} 
    	//You generally DO NOT want to be setting a session attribute over and
    	//over again.. but this is just an example.
    	l_session.setAttribute("name", c_name);
    	
    	// Note: this part generally isn't necessary since LocaleManager
    	// Handles all this part for us.
    	c_locale = l_request.getParameter("locale");
    	if (c_locale == null) {
        	c_locale = (String) l_session.getAttribute("locale");
        	if (c_locale == null) {
        		c_locale = (String)l_request.getHeader("Accept-Language");
        	} 
    	}
    	l_session.setAttribute("locale", c_locale);    	
    	
    	
        return new ForwardResolution(VIEW);
    }

    
    private ActionBeanContext c_ctx;
    public ActionBeanContext getContext() { 
    	return c_ctx; 
    }
    public void setContext(ActionBeanContext p_ctx) { 
    	this.c_ctx = p_ctx; 
	}
}
