package org.scantegrity.sws.action;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.Enumeration;
import java.util.Scanner;

import net.sourceforge.stripes.action.DefaultHandler;
import net.sourceforge.stripes.action.Resolution;

import javax.servlet.http.HttpSession;
import org.apache.commons.lang.StringEscapeUtils;

public class StaticActionBean extends DefaultActionBean {
	
	protected String c_htmlPath;
	
	public StaticActionBean()
	{
		super();
		c_htmlPath = "";
	}
	
	public StaticActionBean(String p_htmlPath)
	{
		c_htmlPath = p_htmlPath;
	}
	
	public String getHtml()
	{
		String l_html = "";
		try {
			String l_htmlPath = c_ctx.getServletContext().getRealPath("/WEB-INF/pages/");
			if( l_htmlPath.charAt(l_htmlPath.length() - 1) != File.separatorChar )
				l_htmlPath = l_htmlPath + File.separator;
			
			l_htmlPath = l_htmlPath + c_htmlPath;
			Scanner l_reader = new Scanner(new BufferedReader(new InputStreamReader(new FileInputStream(l_htmlPath))));
			l_html = l_reader.useDelimiter("\\Z").next(); 
			l_reader.close();
			l_html =  l_html.replace("${pageContext.request.contextPath}", getContext().getServletContext().getContextPath());
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			StringWriter l_writer = new StringWriter();
			e.printStackTrace(new PrintWriter(l_writer));
			return l_writer.toString();
		}
		HttpSession c_sess = getContext().getRequest().getSession(true);
		if( c_sess.getAttribute("username") != null )
		{
			l_html = StringEscapeUtils.escapeHtml(l_html);
			l_html = "<form method='post'><textarea name='editor1'>" + l_html + "</textarea><script type=\"text/javascript\">CKEDITOR.replace( 'editor1' );</script><input type=\"submit\"></form>";
		}
		return l_html;
	}
	
	@Override
	public Resolution view()
	{
		String[] l_values = c_ctx.getRequest().getParameterValues("editor1");
		if( l_values != null && l_values.length > 0 && l_values[0] != null && c_ctx.getRequest().getSession(true).getAttribute("username") != null )
			setHtml(l_values[0]);
		return super.view();
	}
	
	public void setHtml(String p_html)
	{
		try{
			String l_htmlPath = c_ctx.getServletContext().getRealPath("/WEB-INF/pages/") + c_htmlPath;
			BufferedWriter l_writer = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(l_htmlPath)));
			l_writer.write(p_html);
			l_writer.close();
		}
		catch(FileNotFoundException e)
		{
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

}
