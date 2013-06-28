<%@page import="com.logicacmg.koa.databeheer.command.*,com.logicacmg.koa.databeheer.dataobjects.*,java.util.*,java.text.*,com.logicacmg.koa.constants.FunctionalProps" %>
<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN">
<HTML>
<script language="javascript">

function open_child(p_link, p_name)
{
	child_handle=window.open('about:blank', p_name, 'menubar=yes,location=no,scrollbars=yes,resizable=yes,height=550,width=816,statusbar=yes,screenX=100,screenY=100,top=100,left=100');
	
	if(child_handle) child_handle.close();
	
	child_handle=window.open(p_link, p_name, 'menubar=yes,location=no,scrollbars=yes,resizable=yes,height=550,width=816,statusbar=yes,screenX=100,screenY=100,top=100,left=100');

}
	
</script>

<HEAD>
<META name="GENERATOR" content="IBM WebSphere Studio">
<META http-equiv="Pragma" content="no-cache"/>
<META http-equiv="Expires" content="-1"/>
<TITLE>Kiezen op afstand - Databeheer functionaliteit</TITLE>
<LINK href="DatabeheerWeb.css" rel="stylesheet" type="text/css">
</HEAD>
<BODY>
<%
	SelectExportCommand command = 
		(SelectExportCommand) request.getAttribute(CommandConstants.COMMAND_IN_REQUEST_KEY);
	
	Vector exportItems = command.getExportItems();
	
	DateFormat df = DateFormat.getDateTimeInstance();
	String reportName = null;
%>
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
							<strong>Verkiezing voor de leden van het Europees Parlement 2004</strong></font>
						</div>
					</td>
				</tr>
				</table>
			</div></td>  
	</tr>
</table>
<br>
<table align=center border=1 width=600>
<tr>
<td><font face="arial" size="2"><b>Rapport:</b></font></td>
<td><font face="arial" size="2"><b>Tijdstip:</b></font></td>
</tr>
<%
	SimpleDateFormat xSdf = new SimpleDateFormat("dd-MM-yyyy HH:mm:ss");
	
	if (exportItems != null) {
		Enumeration enum = exportItems.elements();
		ExportItem item = null;
		while (enum.hasMoreElements()) {
			item = (ExportItem) enum.nextElement();
			
			if ((item.getType().equals(FunctionalProps.VW_ADD_KIEZERS))
				|| (item.getType().equals(FunctionalProps.VW_REPLACE_KIEZERS))			
				|| (item.getType().equals(FunctionalProps.VW_REPLACE_KANDIDATENLIJST))
				|| (item.getType().equals(FunctionalProps.VW_REMOVE_KIEZERS))
				) {
				reportName = "verwerkingsverslag";
			} else {
				reportName = "export";
			}

			String rptNaam = FunctionalProps.getProperty(item.getType());
			
		
%>
		<tr>
<%
		if (reportName.equals("export")) {
%>
		<td><font face="arial" size="2"><a href="Report?report=<%= reportName %>&id=<%= item.getId()%>"><%= rptNaam %></a></font></td>
<%
		} else {
%>
		<td><font face="arial" size="2"><a href="javascript:open_child('Report?report=<%= reportName %>&id=<%= item.getId()%>','')"><%= rptNaam %></a></font></td>
<%
		}
%>
		<td><font face="arial" size="2"><%= df.format(item.getDate())%></font></td>

		</tr>	
<%
		}	
	}	
	
%>
</table>
<table width="725" border="0" align="center" cellpadding="0" cellspacing="5">
  <tr>
     <td align="left"><BUTTON STYLE="width:200" ONCLICK="window.location='index.jsp'">Terug naar hoofdpagina</BUTTON>
    </td>
  </tr>
</table>
<table width="725" border="0" align="center" cellpadding="0" cellspacing="0">
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