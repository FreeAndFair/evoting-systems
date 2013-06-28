<%@page import="com.logicacmg.koa.voorzitter.command.*,com.logicacmg.koa.constants.*"%>

<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN">
<HTML>

<%
	com.logicacmg.koa.voorzitter.command.FetchDataCommand xCommand = (FetchDataCommand) request.getAttribute(CommandConstants.COMMAND_IN_REQUEST_KEY);
	
	String sDutchCurrentState = "Niet bekend";
	if (xCommand != null)
	{
		sDutchCurrentState = SystemState.getDutchTranslationForState(xCommand.getCurrentState());	
	}
%>
<HEAD>
<META name="GENERATOR" content="IBM WebSphere Studio">
<META http-equiv="Pragma" content="no-cache"/>
<META http-equiv="Expires" content="-1"/>
<META http-equiv="Refresh" content="60;URL=Index" />
<TITLE>Kiezen op afstand - Voorzitter - Ophalen gegevens</TITLE>
<LINK href="VoorzitterWeb.css" rel="stylesheet" type="text/css">
</HEAD>
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
                <td width="3%" align="left" height="380"><img src="images/blueline_3.gif" width="1" height="380"></td>
                <td width="94%" valign="top" height="360">
                <table width="100%" height="100%">
                	<tr><td>Welkom op de 'Ophalen gegevens' pagina van het Internet- en telefoonstembureau.</td></tr>
                	<tr><td>De huidige systeemstatus is: <b><%= sDutchCurrentState %></b></td></tr>
                	<%
        				if( (xCommand == null) ||
        				    (xCommand.getCurrentState().equals(SystemState.CLOSED) 	                          == false	&& 
        					 xCommand.getCurrentState().equals(SystemState.READY_TO_COUNT)                    == false	&&
        					 xCommand != null && xCommand.getCurrentState().equals(SystemState.VOTES_COUNTED) == false) ) 
        				{
        			%>
                           <tr><td>In deze status zijn er geen gegevens beschikbaar om op te halen.</td></tr>
        			<%
        			    } else {
        			%>
	                	<tr><td>Maak een keuze uit een van onderstaande opties:</td></tr>
	                	<tr>
	                	  <td valign="top">
	                		<ul>
	                			<% 
	                				if(xCommand != null && xCommand.getCurrentState().equals(SystemState.VOTES_COUNTED))
	                				{
	                			%>
	                			    <!-- Or 22.3.632 save xml document under a specific name, not standard Report -->
	                				<li><a href="Report?report=uitslag_export">Exportbestand resultaat van de stemming</A></li>
	                				<li><a href="Report?report=transactiecodes">Exportbestand transactie codes</A></li>
	                			<%  } %>
	                			<%
		                			//OR22.3.604 Exporteren versleutelde stembus
	                				if( xCommand != null && xCommand.getCurrentState().equals(SystemState.CLOSED) 			|| 
	                					xCommand != null && xCommand.getCurrentState().equals(SystemState.READY_TO_COUNT) 	||
	                					xCommand != null && xCommand.getCurrentState().equals(SystemState.VOTES_COUNTED) 		) 
	                				{
	                			%>
	                				<!-- Or 22.3.632 save xml document under a specific name, not standard Report -->
	                 				<li><a href="Report?report=versleutelde_stembus_export">Exportbestand versleutelde stembus</A></li>
	                			<%	} %>
	                		</ul>
	                      </td>
	                    </tr>
	                <%  } %>
                    <tr>
                      <td align="left">
                        <BUTTON STYLE="width:200" ONCLICK="window.location='Index'">Terug naar statusoverzicht</BUTTON>
                      </td>
                    </tr>
                </table>
		      </td>
		      <td width="3%" align="right" height="380"><img src="images/blueline_3.gif" width="1" height="380"></td>
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
</BODY>
<HEAD>
<META http-equiv="Pragma" content="no-cache" />
<META http-equiv="Expires" content="-1" />
</HEAD>
</HTML>