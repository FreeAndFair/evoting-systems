<%@page import="com.logicacmg.koa.controller.client.ClientManager"%>
<%@page import="com.logicacmg.koa.constants.SystemState"%>
<%@page import="com.logicacmg.koa.constants.ComponentType"%>
<%@page import="com.logicacmg.koa.constants.FunctionalProps"%>
<%@page session="false" %>
<%
	response.setHeader("Pragma", "no-cache"); //http1.0
	response.setHeader("Cache-Control", "no-cache"); //http1.1
%>
<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1">
<META name="GENERATOR" content="IBM WebSphere Studio">
<META http-equiv="Pragma" content="no-cache"/>
<META http-equiv="Expires" content="-1"/>
<LINK href="KiezerWeb.css" rel="stylesheet" type="text/css">
<TITLE>Verkiezing voor de leden van het Europees Parlement 2004</TITLE>
</head>

<%
	String sCurrentState = ClientManager.getLocalState (ComponentType.WEB);
	String sElectionText = SystemState.getWebTextForState (sCurrentState);	
%>

<body>

        <table width="725" border="0" align="center" cellpadding="0" cellspacing="0">
            <tr>
                <td colspan="3"><div align="left">
              <table width="100%" border="0" cellspacing="0" cellpadding="0">
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
                <div align="center">&nbsp;
                <table width="100%" border="0" cellpadding="3">
                    <tr>
                    	<td>
                        <p align="left"><font size="2">Het uitbrengen van uw stem 
                    verloopt in vier stappen:</font>
                  <ol>
                    <li><font size="2">Allereerst wordt u gevraagd uw stemcode 
                      en toegangscode in te voeren.</font></li>
                    <li><font size="2">De tweede stap bestaat uit het invoeren 
                      van de kandidaatcode die vermeld is bij de kandidaat van 
                      uw keuze. Het is noodzakelijk om het overzicht van kandidatenlijsten 
                      (dat aan u is toegezonden) hiervoor bij de hand te houden.</font></li>
                    <li><font size="2">De derde stap bestaat uit het bevestigen 
                      van uw keuze. Uw stem is pas daadwerkelijk uitgebracht zodra 
                      uw bevestiging is ontvangen.</font></li>
                 <%
					String show_transactioncode = FunctionalProps.getProperty(FunctionalProps.SHOW_TRANSACTIONCODE);
					if( show_transactioncode != null &&
					    show_transactioncode.equalsIgnoreCase("NO") == true )
					{
                 %>
                    <li><font size="2">Tenslotte ontvangt u de mededeling dat u gestemd heeft.</font></li>
                 <% }
                    else {
                 %>
                    <li><font size="2">Tenslotte ontvangt u een transactiecode.</font></li>
                 <% } %>
                        </ol>
                       </p>
<%
	if (sElectionText != null) 
	{
%>
                        <p><b><%= sElectionText %></b></p>           
<%
    } else {
%>                        
                        <p><b>&nbsp;</b></p>           
<%
    } 
%>

                        <p>&nbsp;</p>
                        <p>&nbsp;</p>
                        <p>&nbsp;</p>
                        </td>
                    </tr>
                </table>
                <table width="100%" border="0" cellpadding="3">
                    <tr>
                      <td width="173" height="38"><a href="index.jsp"><img src="images/terug_2.gif" width="108" height="46" border="0" alt="druk hierop om terug te gaan naar de vorige pagina"></a></td>
                      <td height="38">&nbsp;</td>
<%
	/* Do not show "Verder" button if not open. */
	if (SystemState.OPEN.equals(sCurrentState)) 
	{
%>                
                        <td height="38">
                        <div align="right"><a href="identification.jsp"><img src="images/verder_3.gif" width="108" height="46" border="0" alt="druk hierop indien u wilt stemmen"></a></div>
                        </td>
<%
	}
%>                
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
<HEAD>
<META http-equiv="Pragma" content="no-cache"/>
<META http-equiv="Expires" content="-1"/>
</HEAD>
</html>
