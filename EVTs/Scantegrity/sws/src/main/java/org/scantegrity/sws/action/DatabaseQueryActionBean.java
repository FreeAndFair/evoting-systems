package org.scantegrity.sws.action;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.ResultSet;
import java.sql.ResultSetMetaData;
import java.sql.SQLException;
import java.sql.Statement;
import java.sql.Types;

import org.scantegrity.sws.action.DAOFactory;

import net.sourceforge.stripes.action.DefaultHandler;
import net.sourceforge.stripes.action.ForwardResolution;
import net.sourceforge.stripes.action.Resolution;
import net.sourceforge.stripes.validation.Validate;

public class DatabaseQueryActionBean extends RestrictedActionBean {
	String c_dbRes = "";
	@Validate(required=true) String c_queryText;
	
	public String getQuery(){ return c_queryText; }
	public void setQuery(String p_query) { c_queryText = p_query; }
	
	public String getResults()
	{
		return c_dbRes;
	}
	
	public void setResults(String p_res)
	{
		c_dbRes = p_res;
	}
	
	@DefaultHandler
	public Resolution submit()
	{
		Resolution l_userCheck = super.checkUser();
		if( l_userCheck != null ) return l_userCheck;
		
		if( c_queryText == null || c_queryText.isEmpty() )
			return new ForwardResolution("/WEB-INF/pages/databasequery.jsp");
		
		try {
			//get connection to database.
			Connection l_conn = DAOFactory.getInstance().getConnection();

			//Create SQL statement object
			Statement l_query = l_conn.createStatement();
			
			if( !l_query.execute(c_queryText) )
			{
				c_dbRes = l_query.getUpdateCount() + " row(s) successfullly updated.";
			}
			else
			{
				ResultSet l_res = l_query.getResultSet();
				c_dbRes = "<table style='width: 80%;text-align: left'><td>";
				ResultSetMetaData l_meta = l_res.getMetaData();
				for( int x = 1; x <= l_meta.getColumnCount(); x++ )
				{
					c_dbRes += "<th>" + l_meta.getColumnName(x) + "</th>";
				}
				while( l_res.next() )
				{
					c_dbRes += "<tr>";
					for( int x = 1; x <= l_meta.getColumnCount(); x++ )
					{
						c_dbRes += "<td>";
						if( l_meta.getColumnType(x) == Types.VARCHAR )
							c_dbRes += l_res.getString(x);
						else if( l_meta.getColumnType(x) == Types.INTEGER )
							c_dbRes += l_res.getInt(x);
						c_dbRes += "</td>";
					}
					c_dbRes += "</tr>";
				}
				c_dbRes += "</table>";
			}
			
		} catch (Exception e )
		{
			setResults( e.getMessage() );
		}
		finally {}
		return new ForwardResolution("/WEB-INF/pages/databasequery.jsp");
	}

}
