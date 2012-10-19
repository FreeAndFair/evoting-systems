package org.scantegrity.sws.action;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.SQLException;
import java.sql.Statement;

import org.scantegrity.sws.action.DAOFactory;

import net.sourceforge.stripes.action.DefaultHandler;
import net.sourceforge.stripes.action.ForwardResolution;
import net.sourceforge.stripes.action.HandlesEvent;
import net.sourceforge.stripes.action.Resolution;
import net.sourceforge.stripes.action.RedirectResolution;

public class AdminActionBean extends RestrictedActionBean {
		@HandlesEvent(value="logout")
	public Resolution logout()
	{
		c_ctx.getRequest().getSession().invalidate();
		return new RedirectResolution(c_ctx.getServletContext().getContextPath());
	}
	
	@HandlesEvent(value="deleteDatabase")
	public Resolution deleteDatabase()
	{
		try
		{
			Connection l_conn = DAOFactory.getInstance().getConnection();
	
			//Create SQL statement object
			Statement l_query = l_conn.createStatement();
		

			l_query.executeUpdate("DELETE FROM ContestResults");
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
		}
		finally{}
		
		return new ForwardResolution("/WEB-INF/pages/admin.jsp");
	}
	
	@DefaultHandler
	public Resolution submit()
	{
		Resolution l_userCheck = super.checkUser();
		if( l_userCheck != null ) return l_userCheck;
		
		return new ForwardResolution("/WEB-INF/pages/admin.jsp");
	}

}
