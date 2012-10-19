package org.scantegrity.sws.action;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.text.ParseException;
import java.util.ArrayList;
import java.util.NoSuchElementException;
import java.util.Vector;

import org.apache.http.HttpResponse;
import org.apache.http.client.ClientProtocolException;
import org.apache.http.client.methods.HttpGet;
import org.apache.http.conn.params.ConnManagerParams;
import org.apache.http.conn.scheme.SchemeRegistry;
import org.apache.http.impl.client.DefaultHttpClient;
import org.apache.http.params.AbstractHttpParams;
import org.apache.http.params.BasicHttpParams;
import org.apache.http.params.HttpConnectionParams;
import org.scantegrity.sws.action.DAOFactory;

import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.DocumentBuilder;
import org.w3c.dom.Document;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.NodeList;
import org.w3c.dom.Node;
import org.w3c.dom.Element;

import net.sourceforge.stripes.action.ActionBean;
import net.sourceforge.stripes.action.ActionBeanContext;
import net.sourceforge.stripes.action.DefaultHandler;
import net.sourceforge.stripes.action.ForwardResolution;
import net.sourceforge.stripes.action.Resolution;
import net.sourceforge.stripes.validation.Validate;

public class CheckCodesActionBean implements ActionBean {
	
	private static final String c_CompositeURL = "http://128.164.157.181/map?id=%d-%d";
	
	@Validate(required=true) String c_serial;
	ArrayList<ArrayList<String[]>> c_codes = new ArrayList<ArrayList<String[]>>();
	String c_error = "";
	
	public String getResult()
	{
		if( c_codes.size() == 0 )
			return "";
		
		String l_result = "";
		
		for(int x = 0; x < c_codes.size(); x++ )
		{
			l_result += "<div>";
			l_result += "<h4>Contest " + (x + 1) + ": </h4>";
			l_result += "<table style=\"width:60%;\"><tr><th style=\"text-align:left;\">Rank</th><th style=\"text-align:left;\">Code</th></tr>";
			int i = 1;
			for( String[] code : c_codes.get(x) )
			{
				l_result += "<tr>";
				l_result += "<td>" + ((int)(i)) + "</td>";
				l_result += "<td>" + code[1] + "</td>";
				l_result += "</tr>";
				i++;
			}
			l_result += "</table><br/>";
			l_result += "</div>";
		}
		return l_result;
	}
	
	public void setResult(String p_res)
	{
		
	}
	
	public String getErrors()
	{
		return "<div class=\"error\">" + c_error + "</div>";
	}

	public void setErrors(String p_error)
	{
		c_error = p_error;
	}
	
	public String getSerial()
	{
		return c_serial;
	}
	
	public void setSerial(String p_serial)
	{
		c_serial = p_serial;
	}
	
	@DefaultHandler
	public Resolution submit()
	{
		System.setProperty("derby.system.home", "/opt/db-derby");
		if( c_serial == null || c_serial.isEmpty() )
			return new ForwardResolution("/WEB-INF/pages/checkcodes.jsp");
		try
		{ 
			c_codes.clear();
			
			//Create connection to database.  Create database if it doesn't exist.
			Connection l_conn = DAOFactory.getInstance().getConnection();
	
			String l_serialString = c_serial;
			l_serialString = l_serialString.replace("-", "");
			l_serialString = l_serialString.replace(" ", "");
			int l_serial, l_styleID;
			if (l_serialString.length() == 7)
			{
				//Get all the digits but the first for the serial
				l_serial = Integer.parseInt(l_serialString.substring(1));
				//Get the first digit for the style ID
				l_styleID = Integer.parseInt(l_serialString.substring(0, 1));
			}
			else if (l_serialString.length() == 6) 
			{
				//Get all the digits but the first for the serial
				l_serial = Integer.parseInt(l_serialString);
				//Guess that it's ward 1
				l_styleID = 1;
			}
			else
			{
				throw new Exception("Could not find ballot. WebID numbers should be 6 or 7 digits long.");
			}
			
			if (!SetCodesWithComposite(l_styleID, l_serial))
			{
				SetCodesWithDatabase(l_styleID, l_serial);
			}
				

			
			//Create SQL statement object
			Statement l_existQuery = l_conn.createStatement();
			
			//Test to see if the table exists, create it if it doesn't
			/* Now, we just try to select something from the table and if an error is thrown
			 * that contains "does not exist" then we try and create it.  Could be done
			 * better with T-SQL, doesn't handle the case where the table exists but 
			 * doesn't have the columns we are expecting.
			 */
			try
			{
				l_existQuery.execute("SELECT COUNT(*) FROM UserTracking");
			}
			catch( SQLException e )
			{
				if( e.getMessage().contains("does not exist") )
				{
					l_existQuery.execute("CREATE TABLE UserTracking ( ipaddress varchar(20), ballotserial varchar(20) )");
				}
			}
			
			PreparedStatement l_trackingQuery = l_conn.prepareStatement("INSERT INTO UserTracking VALUES (?,?)");
			
			String l_ipaddress = c_ctx.getRequest().getRemoteAddr();
			
			l_trackingQuery.setString(1, l_ipaddress);
			l_trackingQuery.setString(2, c_serial);
			
			l_trackingQuery.executeUpdate();
			l_conn.close();
			
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
		} catch(Exception l_e)
		{
			c_error = l_e.getMessage();
		}
		
		return new ForwardResolution("/WEB-INF/pages/checkcodes.jsp");
	}
	
	/**
	 * Makes a request to the composite server (currently hard-coded, but needs
	 * to go in a properties file). 
	 * 
	 * If the request times out, fails after 5 seconds, or we don't get codes or
	 * xml back, return false. 
	 * 
	 * @param p_styleID
	 * @param p_serial
	 * @return
	 */
	private boolean SetCodesWithComposite(int p_styleID, int p_serial) {
    	try {
    		AbstractHttpParams l_params = new BasicHttpParams();
    	    HttpConnectionParams.setConnectionTimeout(l_params, 5000);
    	    HttpConnectionParams.setSoTimeout(l_params, 5000);
    	    ConnManagerParams.setMaxTotalConnections(l_params, 20);

    	    DefaultHttpClient l_httpClient = new DefaultHttpClient(l_params); 
        	HttpResponse l_resp = l_httpClient.execute(
						new HttpGet(
							String.format(c_CompositeURL, p_styleID, p_serial)
						));
			
			DocumentBuilderFactory l_dbFactory = 
										DocumentBuilderFactory.newInstance();
			DocumentBuilder l_builder = l_dbFactory.newDocumentBuilder();
			Document l_doc = l_builder.parse(l_resp.getEntity().getContent());
			
			ArrayList<String[]> l_newCodes = new ArrayList<String[]>();
			NodeList l_questions = l_doc.getElementsByTagName("question");
			for (int i = 0; i < l_questions.getLength(); i++)
			{
				NodeList l_codes = l_questions.item(i).getChildNodes();
				for (int j = 0; j < l_codes.getLength(); j++)
				{
					if (l_codes.item(j).getNodeName().equals("symbol"))
					{
						NamedNodeMap l_codeAttrs = 
												l_codes.item(j).getAttributes();
						String[] l_code = new String[2]; 
						l_code[0] = 
								l_codeAttrs.getNamedItem("id").getNodeValue(); 
						l_code[1] = 
								l_codeAttrs.getNamedItem("code").getNodeValue();
						l_newCodes.add(l_code);
					}
				}
				if( l_newCodes.size() != 0 )
				{
					c_codes.add(l_newCodes);
					l_newCodes = new ArrayList<String[]>();
				}
			}
			if( c_codes.size() != 0 )
			{
				//c_codes.add(l_newCodes);
				return true;
			}
		} catch (ClientProtocolException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IllegalArgumentException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		// If we reach the end, we failed. 
		return false;
	}

	private void SetCodesWithDatabase(int p_styleID, int p_serial) 
	throws SQLException, InstantiationException, 
			IllegalAccessException, ClassNotFoundException
	{
		Connection l_conn = DAOFactory.getInstance().getConnection();
		//Create SQL statement object
		PreparedStatement l_query = l_conn.prepareStatement("SELECT question,symbol,code FROM ContestResults WHERE serial=? AND ballotstyle=? ORDER BY question,symbol");

		//Get all the digits but the first for the serial
		l_query.setInt(1, p_serial);
		//Get the first digit for the style ID
		l_query.setInt(2, p_styleID);
		
		
		ResultSet l_results = l_query.executeQuery();
		
		int c_question = -1;
		ArrayList<String[]> c_newCodes = new ArrayList<String[]>();
		
		while( l_results.next() )
		{
			int c_newQuestion = l_results.getInt("question");
			if( c_question == -1 )
				c_question = c_newQuestion;
			else if( c_question != c_newQuestion )
			{
				c_codes.add(c_newCodes);
				c_newCodes = new ArrayList<String[]>();
				c_question = c_newQuestion;
			}
			
			String[] c_newCode = new String[2];
			c_newCode[0] = Integer.toString(l_results.getInt("symbol"));
			c_newCode[1] = l_results.getString("code");
			c_newCodes.add(c_newCode);
		}
		if( c_newCodes.size() != 0 )
			c_codes.add(c_newCodes);
		
		l_results.close();
		
		if( c_codes.size() == 0 )
		{
			l_conn.close();
			throw new NoSuchElementException();
		}		
	}
	
	private ActionBeanContext c_ctx;
	public ActionBeanContext getContext() { 
		return c_ctx; 
	}
	public void setContext(ActionBeanContext p_ctx) { 
		this.c_ctx = p_ctx; 
	}
}
