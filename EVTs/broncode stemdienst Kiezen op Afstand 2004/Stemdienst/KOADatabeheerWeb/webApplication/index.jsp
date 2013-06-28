<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN">
<HTML>
<HEAD>
<META name="GENERATOR" content="IBM WebSphere Studio">
<META http-equiv="Pragma" content="no-cache"/>
<META http-equiv="Expires" content="-1"/>
<TITLE>Kiezen op afstand - Databeheer functionaliteit</TITLE>
<LINK href="DatabeheerWeb.css" rel="stylesheet" type="text/css">
</HEAD>

<script language="javascript">

function open_child(p_link, p_name)
{
	child_handle=window.open('about:blank', p_name, 'menubar=yes,location=no,scrollbars=yes,resizable=yes,height=550,width=816,statusbar=yes,screenX=100,screenY=100,top=100,left=100');
	
	if(child_handle) child_handle.close();
	
	child_handle=window.open(p_link, p_name, 'menubar=yes,location=no,scrollbars=yes,resizable=yes,height=550,width=816,statusbar=yes,screenX=100,screenY=100,top=100,left=100');

}
</script>

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
							<strong>Verkiezing voor de leden van het Europees Parlement 2004</strong></font>
						</div>
					</td>
				</tr>
				</table>
			</div></td>  
            </tr>
            <tr valign="top">
                <td width="3%" align="left" height="380"><img src="images/blueline_3.gif" width="1" height="380"></td>
                 <td width="94%" valign="top" height="380">
                	<table width="100%" height="100%" border="0" cellpadding="0" cellspacing="0">
	                	<tr><td colspan="2">Welkom bij de databeheer functionaliteit van KOA.<td></tr>
			            <tr>
			                <td colspan="2">Voor het kiezersbestand zijn de volgende functies beschikbaar:</td>
			            </tr>
			            <tr>
			            	<td width="3%">&nbsp;</td>
			            	<td>
			            	<ul>
			                <li><A href="SelectUpload?<%= com.logicacmg.koa.databeheer.command.SelectUploadCommand.ACTION %>=<%= com.logicacmg.koa.databeheer.command.SelectUploadCommand.VOTER_REPLACE %>">Aanbieden van een vervangend bestand.</A></li>
			                <li><A href="SelectUpload?<%= com.logicacmg.koa.databeheer.command.SelectUploadCommand.ACTION %>=<%= com.logicacmg.koa.databeheer.command.SelectUploadCommand.VOTER_APPEND %>">Aanbieden van een aanvullend bestand.</A></li>
			                <li><A href="SelectUpload?<%= com.logicacmg.koa.databeheer.command.SelectUploadCommand.ACTION %>=<%= com.logicacmg.koa.databeheer.command.SelectUploadCommand.VOTER_REMOVE %>">Aanbieden van een verwijder bestand.</A></li>
			                </ul>
			                </td>
			            </tr>
			            <tr>
			                <td colspan="2">Voor de kandidatenlijst zijn de volgende functies beschikbaar:</td>
			                <td>&nbsp;</td>
			            </tr>
			            <tr>
       			         	<td>&nbsp;</td>   
			                <td><ul><li><A href="SelectUpload?<%= com.logicacmg.koa.databeheer.command.SelectUploadCommand.ACTION %>=<%= com.logicacmg.koa.databeheer.command.SelectUploadCommand.CANDIDATES_REPLACE %>">Aanbieden van een kandidatenlijst</A></li></ul></td>
			            </tr>

			            <TR>
			            	<TD colspan="2">Overige beheersfuncties:</TD>
			            	
			            <TR>
			            	<td>&nbsp;</td>
			            	<TD>
			            		<ul><li><A href="ScheduledJobsOverview">Scheduler overzicht</a></li>
			            	</ul></td>
			            </tr>
			            <TR>
			            	<TD colspan="2">Rapporten:</td>
			            	<td>&nbsp;</td>
			            </tr>
			            <tr>
				            <td>&nbsp;</td>   
			                <td>
			                	<ul>
			                		<li><A href="javascript:open_child('select_teller_historie.jsp','')">Rapport met tellerhistorie</A></li>
			                		<li><A href="javascript:open_child('Report?report=counters_export','')">Export tellers</A></li>
			                		<li><A href="javascript:open_child('Report?report=export_audit','')">Export auditlog</A></li>
			                		<li><A href="SelectExport">Overzicht overige rapporten</A></li>
			                	</ul>
			                </td>
			            </TR>

			        </table>
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
