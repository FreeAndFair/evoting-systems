<%@page import="com.logicacmg.koa.constants.FunctionalProps"%>
<%@page import="com.logicacmg.koa.dataobjects.*"%>
<%@page import="com.logicacmg.koa.votecommands.*"%>
<%@page import="com.logica.eplatform.command.http.*"%>
<%@page import="java.text.*"%>
<%
	response.setHeader("Pragma", "no-cache"); //http1.0
	response.setHeader("Cache-Control", "no-cache"); //http1.1
%>
<% 
   AlreadyVotedCommand xCommand = null;
   
   String sModaliteit = null, sDate = null, sTime = null, sTxID = null;
   
   
   Object xObject = request.getAttribute(CommandConstants.COMMAND_IN_REQUEST_KEY);
   if(xObject != null)
   {
   	  
   	  if(xObject instanceof com.logicacmg.koa.votecommands.AlreadyVotedCommand)
   	  {
         xCommand = (AlreadyVotedCommand) xObject;
         
         Kiezer xKiezer = xCommand.getKiezer();
         
         if(xKiezer != null)
         {
         	sTxID = xKiezer.transactionNumber;
         }
      }
   } 
%>
<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN">
<HTML>
<HEAD>
<TITLE>Verkiezing voor de leden van het Europees Parlement 2004</TITLE>
<META http-equiv="Content-Type" content="text/html; charset=UTF-8">
<META name="GENERATOR" content="IBM WebSphere Studio">
<META http-equiv="Pragma" content="no-cache"/>
<META http-equiv="Expires" content="-1"/>
<LINK href="KiezerWeb.css" rel="stylesheet" type="text/css">
</HEAD>

<body>

<table width="725" border="0" align="center" cellpadding="0" cellspacing="0">
    <tr>
        <td colspan="3">
        <table width="100%" border="0" cellspacing="0" cellpadding="0">
            <tr>

                <td width="640" height="57" bgcolor="#6699CC">
                <div align="center"><font color="#FFFFFF" size="4" face="Arial, Helvetica, sans-serif"><strong>Verkiezing van de leden van het Europees Parlement 2004</strong></font></div>
                </td>
            </tr>
        </table>
        </td>
    </tr>
    <tr valign="top">
        <td width="3%" align="left"><img src="images/blueline_3.gif" width="1" height="380"></td>
        <td width="94%" valign="top">
        <div align="center">&nbsp;
        <table width="100%" border="0" cellpadding="3">
            <tr>
                <%
					String show_transactioncode = FunctionalProps.getProperty(FunctionalProps.SHOW_TRANSACTIONCODE);
					if( show_transactioncode != null &&
					    show_transactioncode.equalsIgnoreCase("NO") == true )
					{
                %>
                <td height="270">
                <p align="center">U heeft uw stem reeds uitgebracht.</p>
                <%  }
                    else {
                %>
                <td height="270">
                <p align="center">U heeft uw stem reeds uitgebracht. Uw transactiecode is <%= sTxID%>.</p>
                <%  } %>
            </tr>
        </table>
        <table width="100%" border="0" cellpadding="3">
            <tr>
                <td width="133"><img src="images/filler.gif" width="218" height="1"></td>
                <td>&nbsp;</td>
                <td>
                <div align="right"></div>
                </td>
            </tr>
        </table>
        </div>

        </td>
        <td width="3%" align="right"><img src="images/blueline_3.gif" width="1" height="380"></td>
    </tr>
    <tr valign="top">
        <td height="1" colspan="3"><img src="images/horizontalline_2.gif" width="726" height="1"></td>
    </tr>
    <tr valign="top">
        <td colspan="3">
        <div align="center">
        <H2>De verantwoordelijkheid voor deze site berust bij het ministerie van Binnenlandse Zaken en Koninkrijksrelaties</H2>
        </div>
        </td>
    </tr>
</table>

</body>


<%
	// After voting make sure the session is invalidated.
	try
	{
		session.invalidate();
	}
	catch (IllegalStateException ise)
	{
		//session is already invalidated
	}

%>

<HEAD>
<META http-equiv="Pragma" content="no-cache"/>
<META http-equiv="Expires" content="-1"/>
</HEAD>
</HTML>
