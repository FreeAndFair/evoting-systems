package org.scantegrity.sws.action;

import net.sourceforge.stripes.action.ActionBean;
import net.sourceforge.stripes.action.ActionBeanContext;
import net.sourceforge.stripes.action.DefaultHandler;
import net.sourceforge.stripes.action.ForwardResolution;
import net.sourceforge.stripes.action.Resolution;

public class HelloActionBean implements ActionBean {
    private static final String VIEW = "/WEB-INF/pages/hello.jsp";
	
    private String hello;
    public String getHello() {
        return hello;
    }

    @DefaultHandler
    public Resolution hello() {/* (3) */
    	hello = "Hello World!";
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

