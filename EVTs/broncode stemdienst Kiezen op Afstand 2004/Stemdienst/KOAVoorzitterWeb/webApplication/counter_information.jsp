<%@page import="com.logicacmg.koa.voorzitter.command.*,java.util.*,com.logicacmg.koa.dataobjects.CounterData, com.logicacmg.koa.constants.*" %>
<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN">
<HTML>
<HEAD>
<META name="GENERATOR" content="IBM WebSphere Studio">
<META http-equiv="Pragma" content="no-cache"/>
<META http-equiv="Expires" content="-1"/>
<TITLE>Kiezen op afstand - Voorzitter - Tellerstanden</TITLE>
<LINK href="VoorzitterWeb.css" rel="stylesheet" type="text/css">
</HEAD>
<%
	GetCurrentCounterCommand command = 
		(GetCurrentCounterCommand) request.getAttribute(CommandConstants.COMMAND_IN_REQUEST_KEY);
	
	Vector vCurrentCounters = command.getCurrentCounters();
	Enumeration enum = vCurrentCounters.elements();
	
	
%>
<BODY>
        <table width="725" border="0" align="center" cellpadding="0" cellspacing="0">
            <tr>
            	<td colspan="3" background="images/banner_filler.gif"><div align="left">
					<table width="100%" border="0" cellspacing="0" cellpadding="0">
					<tr>
						<td width="76" height="57">
							<div align="left"><IMG src="images/leeuw.gif" width="76" height="57" border="0"></div>
						</td>
						<td width="640" height="57">
							<div align="center"><font color="#FFFFFF" size="4" face="Arial, Helvetica, sans-serif">
								<strong>Verkiezing van de leden van het Europees Parlement 2004</strong></font>
							</div>
						</td>
					</tr>
					</table>
				</div></td>  
            </tr>
            <tr valign="top">
                <td width="94%" valign="top">
                <table width="100%" height="100%" border="0">
                	<tr><td colspan="4"><H1>Tellerstanden</H1></td></tr>
						<%
							boolean bShowDateTime = true;
							while (enum.hasMoreElements())
							{ 
								CounterData xData = (CounterData) enum.nextElement();
								Enumeration keyEnum = xData.getCounterKeys();
						
								//OR22.3.77 show date/time for counters when shown first time
								if (bShowDateTime) 
								{
									bShowDateTime = false;
						%>
				                	<tr><td colspan="4">Opgehaald om <%= xData.getTimestamp() %></td></tr>
									<TR bgcolor="#CCCCCC"><TD width="100%" colspan="4"><img src="images/filler.gif" width="1" height="1"></TD></TR>
				        <%
								}
						%>
						<tr><td colspan="4"><b><%= command.translateComponent(xData.getComponentType()) %></b></td></tr>
						<%			
						
								while (keyEnum.hasMoreElements())
								{
									String sCounterKey = (String) keyEnum.nextElement();
						%>
						
						<tr>
							<td>&nbsp;</td>
							<td><%= command.translateCounterKey(sCounterKey) %></td>
							<td>=</td>
							<td><%= Long.toString (xData.getCounter(sCounterKey)) %></td>
						</tr>
						
						<%			
								}
							}
						%>
				    <tr>
				      <td width="100%" colspan="4"><img src="images/filler.gif" width="1" height="1">
				      </td>
				    </tr>
                	<tr>
                	  <td colspan="4" align="left"><BUTTON STYLE="width:200" ONCLICK="window.location='Index'">Terug naar statusoverzicht</BUTTON>
                	  </td>
                	</tr>
                  </table>
				</td>
			</tr>
			<tr valign="top">
                <td colspan="3" height="10"><img src="images/horizontalline_2.gif" width="726" height="1"></td>
            </tr>
            <tr valign="top">
                <td colspan="3">
                <div align="center">
                <H2>De verantwoordelijkheid voor deze site berust bij het ministerie van Binnenlandse Zaken en Koninkrijksrelaties</H2>
                </div>
                </td>
            </tr>
		</table>
		
	<%@ include file="refreshFooter.jsp" %>		
</BODY>
<HEAD>
<META http-equiv="Pragma" content="no-cache" />
<META http-equiv="Expires" content="-1" />
</HEAD>
</HTML>