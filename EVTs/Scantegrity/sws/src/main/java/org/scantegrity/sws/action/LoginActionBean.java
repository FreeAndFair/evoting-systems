package org.scantegrity.sws.action;

import java.io.IOException;
import java.sql.SQLException;

import javax.servlet.http.HttpSession;

import net.sourceforge.stripes.action.ActionBean;
import net.sourceforge.stripes.action.ActionBeanContext;
import net.sourceforge.stripes.action.DefaultHandler;
import net.sourceforge.stripes.action.ForwardResolution;
import net.sourceforge.stripes.action.RedirectResolution;
import net.sourceforge.stripes.action.Resolution;
import net.sourceforge.stripes.validation.SimpleError;
import net.sourceforge.stripes.validation.Validate;
import net.sourceforge.stripes.validation.ValidationErrors;
import net.sourceforge.stripes.validation.ValidationMethod;

public class LoginActionBean implements ActionBean {
	private static final String VIEW = "/WEB-INF/pages/login.jsp";
	
	@Validate(required=true) String c_user;
	@Validate(required=true) String c_pass;
	String c_error = "";
	
	public String getUsername()
	{
		return c_user;
	}
	public void setUsername(String p_user)
	{
		c_user = p_user;
	}
	
	public String getPassword()
	{
		return c_pass;
	}
	public void setPassword(String p_pass)
	{
		c_pass = p_pass;
	}
	
	public String getErrors()
	{
		return "<div class=\"error\">" + c_error + "</div>";
	}

	public void setErrors(String p_error)
	{
		c_error = p_error;
	}
	
	protected ActionBeanContext c_ctx;
	public ActionBeanContext getContext() {
		// TODO Auto-generated method stub
		return c_ctx;
	}

	public void setContext(ActionBeanContext arg0) {
		// TODO Auto-generated method stub
		c_ctx = arg0;
	}
	
	@ValidationMethod(on="submit")
	public void checkUser(ValidationErrors errors)
	{
		if( c_pass == null || c_user == null )
			return;
		
		
		
		boolean pass = false;
		try {
			UserManage.addUser("default", "scantegrity");
			pass = UserManage.queryUser(c_user, c_pass);
		} catch (InstantiationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IllegalAccessException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (ClassNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (SQLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		if( !pass )
		{
			errors.add("password", new SimpleError("User name or password incorrect."));
		}
	}
	
	@DefaultHandler
	public Resolution submit()
	{
		if( c_pass == null || c_user == null )
			return new ForwardResolution(VIEW);
		
		HttpSession l_sess = c_ctx.getRequest().getSession(true);
		l_sess.setAttribute("username", c_user);

		String l_redir = (String) l_sess.getAttribute("redir");
		if( l_redir == null || l_redir == "" )
		{
			l_redir = "index";
		}
		return new RedirectResolution(l_redir, false);
	}

}
