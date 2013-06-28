<%@page import="com.logicacmg.koa.controller.client.ClientManager"%>
<%@page import="com.logicacmg.koa.constants.SystemState"%>
<%@page import="com.logicacmg.koa.constants.ComponentType"%>
<%@page session="false" %>
<%
	response.setHeader("Pragma", "no-cache"); //http1.0
	response.setHeader("Cache-Control", "no-cache"); //http1.1
%>
<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN">
<html>
<head>
<title>Verkiezing voor de leden van het Europees Parlement 2004</title>
<meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1">
<META name="GENERATOR" content="IBM WebSphere Studio">
<LINK href="KiezerWeb.css" rel="stylesheet" type="text/css">
<META http-equiv="Pragma" content="no-cache"/>
<META http-equiv="Expires" content="-1"/>
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
                  <!-- <td width="85" bgcolor="#6699CC"><div align="left"><img src="images/eu_logo.gif" width="85" height="57"></div></td>
                 --> 
            <td width="640" height="57" bgcolor="#6699CC">
<div align="center"><font color="#FFFFFF" size="4" face="Arial, Helvetica, sans-serif"><strong>Verkiezing van de leden van het Europees Parlement 2004
                </strong></font></div></td>
                </tr>
              </table>
            </div></td>
            </tr>
            <tr valign="top">
                <td width="3%" align="left"><img src="images/blueline_3.gif" width="1" height="380"></td>
                <td width="94%" valign="top">
                <div align="center">&nbsp;
                <div align="center">
                <center>
                <table width="100%" border="0" cellpadding="3">
                    <tr>
                        <td height="270">
                        <p align="left"><font size="2">Welkom bij het internetstembureau 
                          voor de verkiezing van de leden van het Europees Parlement. 
                          </font></p>
						<p align="left"><font size="2">De mogelijkheid om te stemmen
                          via internet is voorbehouden aan:</font></p>
                        <ul>
                          <li><font size="2">Nederlanders die in het buitenland 
                            wonen</font></li>
                          <li><font size="2">In Nederland wonende kiesgerechtigden 
                            die op de dag van stemming (10 juni 2004) wegens beroep 
                            of werkzaamheden in het buitenland verblijven, alsmede 
                            hun daar verblijvende gezinsleden.</font></li>
                        </ul>
 
                  		<p align="left"><font size="2">Om via internet te kunnen stemmen, dient 
                    		u zich te laten registreren. Zie www.ukomttochook.nl 
                    		voor meer informatie over de registratieprocedure.</font></p>
                                                                       
                        <p align="left"><font size="2">U kunt uw stem uitbrengen 
                          tot donderdag 10 juni 2004, 21:00 uur (Nederlandse tijd).</font></p>
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
                        <p></p>
                        </td>
                    </tr>
                </table>
                </center>
                </div>
<%
	if (SystemState.OPEN.equals(sCurrentState)) 
	{
%>
                <table width="100%" border="0" cellpadding="3">
                    <tr>
                        <td width="133"><img src="images/filler.gif" width="218" height="1"></td>
                        <td height="38">&nbsp;</td>
                        <td height="38">
                        <div align="right"><a href="uitleg.jsp"><img src="images/verder_3.gif" width="108" height="46" border="0" alt="Druk hierop om naar de uitleg te gaan"></a></div>
                        </td>
                    </tr>
                </table>
<%
	}
%>
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
</HTML>
