<%@page import="com.logicacmg.koa.constants.FunctionalProps"%>
<%@page import="com.logica.eplatform.ticket.TicketConstants"%>
<%@page import="com.logicacmg.koa.votecommands.*"%>
<%@page import="com.logicacmg.koa.controller.client.ClientManager"%>
<%@page import="com.logicacmg.koa.constants.SystemState"%>
<%@page import="com.logicacmg.koa.constants.ComponentType"%>
<%-- note: session is not removed, but no session object is explicitly requested here --%>
<%@page session="false" %> 
<%
	/*Note: we check here if we have a session already, if we have one, try to remove the ticket!*/
	HttpSession session = request.getSession(false);
	if (session!=null) {
		try {
			session.removeAttribute(TicketConstants.TICKET_IN_SESSION);
		} catch (Exception e) {
			//ignore
		}
	}

	response.setHeader("Pragma", "no-cache"); //http1.0
	response.setHeader("Cache-Control", "no-cache"); //http1.1
%>
<% 
	String sErrorMessage= null;
	
	if(request.getAttribute(CommandConstants.INLOG_ERROR) != null)
	{
		//System.out.println("casting");
		sErrorMessage = (String) request.getAttribute(CommandConstants.INLOG_ERROR);
	}
	
	String sCurrentState = ClientManager.getLocalState (ComponentType.WEB);
	String sElectionText = SystemState.getWebTextForState (sCurrentState);	
	if (sElectionText == null)
	{
		sElectionText = "&nbsp;";
	}	
	
%>
<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN">
<HTML>
<HEAD>
<META http-equiv="Content-Style-Type" content="text/css">
<META name="GENERATOR" content="IBM WebSphere Studio">
<META http-equiv="Pragma" content="no-cache"/>
<META http-equiv="Expires" content="-1"/>
<LINK href="KiezerWeb.css" rel="stylesheet" type="text/css">
<TITLE>Verkiezing voor de leden van het Europees Parlement 2004</TITLE>
</HEAD>

<body>
<FORM method="post" action="Login<%--Ticket--%>">

        <table width="725" border="0" align="center" cellpadding="0" cellspacing="0">
            <tr>
                <td colspan="3">              <table width="100%" border="0" cellspacing="0" cellpadding="0">
                <tr>
                  <td width="640" height="57" bgcolor="#6699CC">
<div align="center"><font color="#FFFFFF" size="4" face="Arial, Helvetica, sans-serif"><strong>Verkiezing van de leden van het Europees Parlement 2004
                      </strong></font></div></td>
                </tr>
              </table></td>
            </tr>
            <tr valign="top">
                <td width="3%" align="left"><img src="images/blueline_3.gif" width="1" height="380"></td>
                <td width="94%" valign="top">
                <div align="center"><br>
                <table width="100%" border="0" cellpadding="3" height="267">
                  <tr>
	                <%
						String show_transactioncode = FunctionalProps.getProperty(FunctionalProps.SHOW_TRANSACTIONCODE);
						if( show_transactioncode != null &&
						    show_transactioncode.equalsIgnoreCase("NO") == true )
						{
	                %>
                        <td width="200" rowspan="2"><img src="images/orderfull_1_without_transactioncode.gif" width="195" height="120"></td>
	                <%  }
	                    else {
	                %>
                        <td width="200" rowspan="2"><img src="images/orderfull_1.gif" width="195" height="120"></td>
	                <%  } %>
                        <td width="10" rowspan="2"><img src="images/blueline_2.gif" width="2" height="200"></td>
                        <td>
                        <H1>Identificatie</H1>
                        </td>
                    </tr>
                    <tr>
                        
                    <td width="100%" height="230" valign="top"><p><font size="2">Voer uw stemcode 
                        en toegangscode in. De toegangscode heeft u zelf opgegeven
                        op het registratieformulier, de stemcode heeft u tegelijk
                        met het overzicht van kandidatenlijsten toegezonden gekregen. 
                        </font></p>
                        <table width="100%" border="0" cellpadding="5">
                            <tr>
                                
                          <td width="27%"><font size="2">Stemcode:</font></td>
                                <td width="73%"><input type="text" name="USER" maxlength="9"></td>
                            </tr>
                            <tr>
                                
                          <td><font size="2">Toegangscode:</font></td>
                                <td><input type="password" name="PWD" maxlength="5"></td>
                            </tr>
                            <tr>
                               <%                                   
                                  if(sErrorMessage != null)
                                  { 
                               %>
                                  	<td colspan="2"><H3><%= sErrorMessage%></H3></td>
                               <% }
                                  else
                                  {  
                                  %>
                                     <td colspan="2"><b><%= sElectionText %></b></td>
                                <%}%>
                                
                            </tr>
                        </table>
                        <P>&nbsp;</P>
                        </td>
                    </tr>
                </table>
                <table width="100%" border="0" cellpadding="3">
                    <tr>
                        <td width="173" height="38"><a href="uitleg.jsp"><img src="images/terug_2.gif" width="108" height="46" border="0" alt="druk hierop om terug te gaan naar de vorige pagina"></a></td>
                        <td height="38">&nbsp;</td>
                        <td height="38">
                        <div align="right"><input type="image" src="images/verder_3.gif" width="108" height="46" border="0" alt="druk op verder om te kunnen stemmen"></div>
                        </td>
                    </tr>
                </table>
                </div>
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

</form>
</body>
<HEAD>
<META http-equiv="Pragma" content="no-cache"/>
<META http-equiv="Expires" content="-1"/>
</HEAD>
</HTML>
