<%@page import="com.logicacmg.koa.voorzitter.command.*,com.logicacmg.koa.constants.*"%>
<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN">

<HTML>
<%
	com.logicacmg.koa.voorzitter.command.SelectProcesVerbaalCommand xCommand = (SelectProcesVerbaalCommand) request.getAttribute(CommandConstants.COMMAND_IN_REQUEST_KEY);
%>

<HEAD>
<META name="GENERATOR" content="IBM WebSphere Studio">
<META http-equiv="Pragma" content="no-cache"/>
<META http-equiv="Expires" content="-1"/>
<TITLE>Kiezen op afstand - Voorzitter - Selecteer logbestand</TITLE>
<LINK href="VoorzitterWeb.css" rel="stylesheet" type="text/css">
</HEAD>



<BODY>
        <table width="725" border="0" align="center" cellpadding="0" cellspacing="0" valign="middle">
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
                 <td width="94%" valign="top" height="380">
                 	<form action="Report" method="POST">
                 	<input type="hidden" name="report" value="proces_verbaal">
                 	<input type="hidden" name="selection" value="<%=xCommand.getSelection()%>">
                	<table width="100%" height="100%" border="0" cellpadding="0" cellspacing="0">
			            <TR>
			            	<TD colspan="4"><H1>Selectie logbestand</H1></td>
			            </tr>
			            <TR>
			            	<TD colspan="4">Selecteer de periode waarvoor de meldingen uit het logbestand getoond moeten worden:</td>
			            </tr>
			            <tr>
				            <td width="158">Vanaf datum</td>   
			                <td width="12">&nbsp;</td>
			                <td width="330"><input type="text" name="periode_start" size="10" maxlength="10"> formaat: (dd-mm-jjjj)</td>
			                <td width="330"><input type="text" name="periode_start_time" size="5" maxlength="5" value="00:00"> formaat: (uu:mm)</td>
			            </TR>
			            <tr>
				            <td>Tot en met datum</td>   
			                <td>&nbsp;</td>
			                <td><input type="text" name="periode_end" size="10" maxlength="10"> formaat: (dd-mm-jjjj)</td>
			                <td><input type="text" name="periode_end_time" size="5" maxlength="5" value="23:59"> formaat: (uu:mm)</td>
			            </TR>
			            <tr>
			                <td>&nbsp;</td>
			                <td>&nbsp;</td>
			                <td>&nbsp;</td>			                
			                <td align="right">
			                  <input type="submit" name="Toon rapport" value="Toon rapport">
			                </td>
			            </TR>
			        </table>
			        </form>
		       </td>
		       <td width="3%" align="right" height="380"><img src="images/blueline_3.gif" width="1" height="380"></td>
		    </tr>
		    <tr valign="top">
                <td colspan="3" height="20"><img src="images/horizontalline_2.gif" width="726" height="1"></td>
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
<META http-equiv="Pragma" content="no-cache"/>
<META http-equiv="Expires" content="-1"/>
</HEAD>
</HTML>
