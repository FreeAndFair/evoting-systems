

package org.scantegrity.sws.action;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Scanner;

import net.sourceforge.stripes.action.DefaultHandler;
import net.sourceforge.stripes.action.ForwardResolution;
import net.sourceforge.stripes.action.Resolution;

public class ResultsActionBean extends DefaultActionBean{
	
	String c_results = "";
	
	public String getResults()
	{
		return c_results;
	}
	
	public void setResults(String p_results)
	{
		c_results = p_results;
	}
	
	
	
	@DefaultHandler
	public Resolution submit(){
		File l_docsDir = new File(c_ctx.getServletContext().getRealPath("/docs/"));
		String l_useWriteIn = c_ctx.getRequest().getParameter("writein");
		if( l_useWriteIn == null )
			l_useWriteIn = "n";
		File l_results = new File(l_docsDir, l_useWriteIn.equals("y") ? "ResultsRaw.txt" : "Results.txt");
		
		try {
			Scanner l_scanner = new Scanner(l_results);
			while( l_scanner.hasNext() )
			{
				c_results += l_scanner.nextLine() + "\n";
			}
		} catch (FileNotFoundException e) {
		}
		
		
		return new ForwardResolution("/WEB-INF/pages/results.jsp");
	}
}