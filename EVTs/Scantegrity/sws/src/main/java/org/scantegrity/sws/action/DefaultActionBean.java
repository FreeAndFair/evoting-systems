/**
 * This characterizes default behavior for a public page on the site. Extend 
 * this if you want a public page. 
 */

package org.scantegrity.sws.action;

import net.sourceforge.stripes.action.ActionBean;
import net.sourceforge.stripes.action.ActionBeanContext;
import net.sourceforge.stripes.action.DefaultHandler;
import net.sourceforge.stripes.action.DontValidate;
import net.sourceforge.stripes.action.ForwardResolution;
import net.sourceforge.stripes.action.Resolution;

public class DefaultActionBean implements ActionBean {
    private static final String VIEW = "/WEB-INF/pages/";

    @DefaultHandler @DontValidate
    public Resolution view() {
    	String l_name = getClass().getSimpleName();
    	int l_i = l_name.indexOf("Action");
    	//If there is at least 1 char
    	if (l_i > 0) l_name = l_name.substring(0, l_i);
    	else l_name = "index";
    	l_name = l_name.toLowerCase();
        return new ForwardResolution(VIEW + l_name + ".jsp");
    }

    protected void initialize() {}
    
    protected ActionBeanContext c_ctx;
    public ActionBeanContext getContext() { 
    	return c_ctx; 
    }
    public void setContext(ActionBeanContext p_ctx) { 
    	this.c_ctx = p_ctx; 
    	initialize();
	}

}

