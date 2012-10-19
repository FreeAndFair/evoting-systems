package org.scantegrity.sws.action;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.List;
import java.util.NoSuchElementException;

import org.scantegrity.sws.action.DAOFactory;

import net.sourceforge.stripes.action.ActionBeanContext;
import net.sourceforge.stripes.action.DefaultHandler;
import net.sourceforge.stripes.action.ForwardResolution;
import net.sourceforge.stripes.action.HandlesEvent;
import net.sourceforge.stripes.action.Resolution;

public class UserAddActionBean extends RestrictedActionBean {
	private static final String VIEW = "/WEB-INF/pages/useradd.jsp";
	
	private List<String> c_allUsers;
	private String c_error = "";
	private String c_target;
	private String c_newUser;
	private String c_pass;
	
	public String getUsername() { return c_newUser; }
	public void setUsername(String p_user) { c_newUser = p_user; }
	public String getPassword() { return c_pass; }
	public void setPassword(String p_pass) { c_pass = p_pass; }
	
	public String getTarget()
	{
		return c_target;
	}
	public void setTarget(String p_target)
	{
		c_target = p_target;
	}
	
	public List<String> getAllUsers()
	{
		return c_allUsers;
	}
	
	public void setAllUsers(List<String> p_users)
	{
		c_allUsers = p_users;
	}
	
	public String getErrors()
	{
		return "<div class=\"error\">" + c_error + "</div>";
	}

	public void setErrors(String p_error)
	{
		c_error = p_error;
	}
	
	@HandlesEvent(value="addUser")
	public Resolution addUser()
	{
		try
		{
			UserManage.addUser(c_newUser, c_pass);
		} catch (SQLException e) {
			c_error = "Could not execute SQL: " + e.getMessage();
		} catch (InstantiationException e) {
			c_error = "Could not load derby driver: instantiation exception";
		} catch (IllegalAccessException e) {
			c_error = "Could not load derby driver: illegal access exception";
		} catch (ClassNotFoundException e) {
			c_error = "Could not load derby driver: class not found exception";
		} catch (NoSuchElementException e)
		{
			c_error = "Could not locate ballot with given serial. Please try again.";
		}
		
		return submit();
	}
	
	@HandlesEvent(value="deleteUser")
	public Resolution deleteUser()
	{
		try
		{
			UserManage.removeUser(c_target);
		} catch (SQLException e) {
			c_error = "Could not execute SQL: " + e.getMessage();
		} catch (InstantiationException e) {
			c_error = "Could not load derby driver: instantiation exception";
		} catch (IllegalAccessException e) {
			c_error = "Could not load derby driver: illegal access exception";
		} catch (ClassNotFoundException e) {
			c_error = "Could not load derby driver: class not found exception";
		} catch (NoSuchElementException e)
		{
			c_error = "Could not locate ballot with given serial. Please try again.";
		}
		
		return submit();
	}
	
	@DefaultHandler
	public Resolution submit()
	{
		Resolution l_userCheck = super.checkUser();
		if( l_userCheck != null ) return l_userCheck;
		
		
		ArrayList<String> l_users = new ArrayList<String>();
		try
		{
			//Load derby database driver
			Class.forName("org.apache.derby.jdbc.ClientDriver").newInstance();
			//Create connection to database.  Create database if it doesn't exist.
			Connection l_conn = DAOFactory.getInstance().getConnection();
	
			//Create SQL statement object
			PreparedStatement l_query = l_conn.prepareStatement("SELECT username FROM users");
			
			ResultSet l_res = l_query.executeQuery();
			while( l_res.next() )
			{
				l_users.add(l_res.getString("username"));
			}
		} catch (SQLException e) {
			c_error = "Could not execute SQL: " + e.getMessage();
		} catch (InstantiationException e) {
			c_error = "Could not load derby driver: instantiation exception";
		} catch (IllegalAccessException e) {
			c_error = "Could not load derby driver: illegal access exception";
		} catch (ClassNotFoundException e) {
			c_error = "Could not load derby driver: class not found exception";
		} catch (NoSuchElementException e)
		{
			c_error = "Could not locate ballot with given serial. Please try again.";
		}
		c_allUsers = l_users;
		
		return new ForwardResolution(VIEW);
	}
	
	
}
