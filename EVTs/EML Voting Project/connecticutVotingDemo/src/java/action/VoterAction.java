package action;

import forms.VoterForm;

import java.io.File;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.HashMap;
import java.util.Properties;
import javax.servlet.http.*;
import org.apache.struts.action.*;
import propmgr.PropertyLoader;
import util.MessageBean;
import util.PrintBallot;

public class VoterAction extends Action
{
	StringBuffer sb = new StringBuffer();
    public VoterAction()
    {
    } 

    public ActionForward execute(ActionMapping actionmapping, ActionForm actionform, 
    		HttpServletRequest request, HttpServletResponse response)
        throws Exception
    {
        String forwardName = "defaultPage";      
        try{
			String contextPath =null;
			contextPath=request.getContextPath();		
			System.out.println("Context Path "+contextPath);
			String hostName=request.getServerName();
			//pl = new PropertyLoader("http://"+hostName+":8080"+contextPath+"/properties/application.properties");
			pl = new PropertyLoader("http://openvotingsolutions.info/connecticutVotingDemo/properties/application.properties");
			prop=pl.getCache();
		}catch(Exception e) {
			e.printStackTrace();
			sb.append(e.toString());
		}
        try
        {
        	
        	sb.append("realPath "+ request.getRealPath(".")+"\r\n");
        	sb.append("pathinfo "+ request.getPathInfo()+"\r\n");
        	sb.append("context path "+ request.getContextPath()+"\r\n");
        	sb.append("servlet "+ request.getServletPath()+"\r\n");        	
        	
        	writeFile(sb.toString());
        	
            VoterForm voterform = (VoterForm)actionform;                       
            if(request.getParameter("pageAction") != null)
            {
                String pageAction = request.getParameter("pageAction");
                System.out.println("Page Action " + request.getParameter("pageAction"));
                if(pageAction.equals("defaultPage"))
                    voterform.reset(actionmapping, request);
                String barCode = voterform.getBarCode();
                System.out.println("Bar Code " + voterform.getBarCode());
                if(pageAction.equals("barcode") && voterform.getBarCode() != null && voterform.getBarCode().length() > 0)
                {
                    request.getSession().setAttribute("barCode", barCode);
                    forwardName = "success";
                }
                if(pageAction.equals("voteComplete")&& request.getParameter("transactionID") != null)
                {
                	HashMap votedMap = new HashMap();
                	for (int v = 1; v <= 11; v++) {
						if ((request.getParameter("voted"+v) != null) &&
							(request.getParameter("voted"+v).trim().length()>0)){
							
							votedMap.put(v, request.getParameter("voted"+v));
						}
					}
                    barCode = (String)request.getSession().getAttribute("barCode");
                    System.out.println("Vote Complete Bar " + barCode);
                    String transactionID = request.getParameter("transactionID");
                    System.out.println("transactionID " + transactionID);
                    generateBallot(votedMap, transactionID, barCode);
                    request.getSession().removeAttribute("barCode");
                    forwardName = "defaultPage";
                }
                if(pageAction.equals("voteNotComplete"))
                    forwardName = "success";
            }
        }
        catch(Exception exception1)
        {
            exception1.printStackTrace();
        }
        System.out.println("Forward Status " + forwardName);
        return actionmapping.findForward(forwardName);
    }

    public void generateBallot(HashMap votedMap,String transactionID, String barCode)
    {
        try
        {
            StringBuffer stringbuffer = new StringBuffer();
            stringbuffer.append("<?xml version='1.0' encoding='UTF-8'?>\r\n");
            stringbuffer.append("<?xml-stylesheet href=\"http://openvotingsolutions.info/connecticutVotingDemo/xml/connecticutBallot/ballot.xsl\" type=\"text/xsl\"?>\r\n");
            stringbuffer.append("<ballot version=\"1.0\" ID=\"" + transactionID + "\">\r\n");
            for (int i = 1; i <= 11; i++) {
				stringbuffer.append("<column ID=\"" + i + "\" >\r\n");
				for (int j = 1; j <= 7; j++) {
					if ((votedMap.get(i) != null)&& (Integer.parseInt(votedMap.get(i).toString()) == j))
						stringbuffer.append("<checkbox ID=\"" + j+ "\">1</checkbox>\r\n");
					else
						stringbuffer.append("<checkbox ID=\"" + j+ "\">0</checkbox>\r\n");
				}
				stringbuffer.append("</column>\r\n");
			}
            stringbuffer.append("</ballot>\r\n");
            String ballotFolder = prop.getProperty("ballotFolder");
            String ballotImagesFolder = prop.getProperty("ballotImagesFolder");           
            System.out.println("ballotFolder " + ballotFolder);
            String fileName = "ballot"+transactionID+".xml";
            writeFile(ballotFolder+ fileName, stringbuffer.toString());
            PrintBallot printballot = new PrintBallot();
            printballot.createPrintBallot(votedMap, barCode, transactionID, ballotFolder, ballotImagesFolder);
        }
        catch(Exception exception)
        {
            exception.printStackTrace();
        }
    }

    public void writeFile(String fileLocation, String XMLData)
    {
        Object obj = null;
        try
        {
            FileOutputStream fileoutputstream = new FileOutputStream(fileLocation);
            for(int i = 0; i < XMLData.length(); i++)
                fileoutputstream.write(XMLData.charAt(i));

            fileoutputstream.close();
        }
        catch(Exception exception)
        {
            exception.printStackTrace();
        }
    }
    public void writeFile(String XMLData)
    {
    	Object obj = null;
        try
        {
            //FileOutputStream fileoutputstream = new FileOutputStream("ovs.log");
            FileOutputStream fileoutputstream = new FileOutputStream("/home/ovsadmin/public_html/connecticutVotingDemo/ovs.log");
            
            for(int i = 0; i < XMLData.length(); i++)
                fileoutputstream.write(XMLData.charAt(i));

            fileoutputstream.close();
        }
        catch(Exception exception)
        {
            exception.printStackTrace();
        }
    }

    private boolean isMissing(String s)
    {
        return s == null || s.trim().equals("");
    }

    protected void makeWarning(HttpServletRequest request, String s)
    {
        MessageBean messagebean = (MessageBean)request.getAttribute("messageBean");
        messagebean.setMessage(s);
    }

    PropertyLoader pl;
    Properties prop;
}