package org.scantegrity.sws.action;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FilenameFilter;
import java.io.IOException;

import net.sourceforge.stripes.action.ActionBean;
import net.sourceforge.stripes.action.ActionBeanContext;
import net.sourceforge.stripes.action.ForwardResolution;
import net.sourceforge.stripes.action.Resolution;

public class GetFilesActionBean implements ActionBean {
    private static final String VIEW = "/WEB-INF/pages/getfiles.jsp";

	private String c_htmlFiles;
	private String c_error;
	
	public String getErrors()
	{
		return "<div class=\"error\">" + c_error + "</div>";
	}

	public void setErrors(String p_error)
	{
		c_error = p_error;
	}
	
	public String getHtmlFiles()
	{
		return c_htmlFiles;
	}
	
	public void setHtmlFiles(String p_newHtml)
	{
		c_htmlFiles = p_newHtml;
	}
	
    private ActionBeanContext c_ctx;
    public ActionBeanContext getContext() { 
    	return c_ctx; 
    }
    public void setContext(ActionBeanContext p_ctx) { 
    	this.c_ctx = p_ctx; 
	}
    
    public Resolution submit()
    {
    	c_htmlFiles = "";
    	c_htmlFiles += "<table width=\"80%\">";
    	c_htmlFiles += "<tr><th>File Name</th><th>Size</th></tr>";
    	
		try
		{
			File l_docsDir = new File(c_ctx.getServletContext().getRealPath("/docs/"));
			String l_docsPath = c_ctx.getServletContext().getContextPath() + "/docs/";
			if( !l_docsDir.exists() )
			{
				throw new FileNotFoundException("Could not find docs directory.");
			}
			
			File[] l_files = l_docsDir.listFiles(new HiddenFileFilter());
			
			for(File l_newFile : l_files)
			{
				c_htmlFiles += "<tr>";
				c_htmlFiles += "<td><a href=" + l_docsPath + l_newFile.getName() + ">";
				c_htmlFiles += l_newFile.getName() + "</a></td>";
				c_htmlFiles += "<td>" + l_newFile.length() + "</td></tr>";
			}
			c_htmlFiles += "</table>";
		}
		catch(IOException e)
		{
			c_error += e.getMessage() + "\n";
		}
    	
    	return new ForwardResolution(VIEW);
    }
	
    class HiddenFileFilter implements FilenameFilter
    {

		public boolean accept(File dir, String name) {
			return name.charAt(0) != '.';
		}
    	
    }
    
}
