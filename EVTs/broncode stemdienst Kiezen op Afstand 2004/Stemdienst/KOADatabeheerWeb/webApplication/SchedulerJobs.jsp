<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN">

<%@page import="java.util.*"%>
<%@page import="java.text.*"%>
<%@page import="com.logicacmg.koa.utils.*"%>
<%@page import="com.logicacmg.koa.dataobjects.*"%>
<%@page import="com.logicacmg.koa.scheduler.*"%>
<%@page import="com.logicacmg.koa.databeheer.command.*"%>

<%

	ScheduledJobsAdministrationCommand command = (ScheduledJobsAdministrationCommand)request.getAttribute("COMMAND");
	ScheduledJobsAdministrationObject overview = (ScheduledJobsAdministrationObject) command.getOverview();
	
	final SimpleDateFormat dateFormat = new SimpleDateFormat(SchedulerConstants.DATE_FORMAT);
%>

<!-- Spacer image -->
<HEAD>
<META name="GENERATOR" content="IBM WebSphere Studio">
<META http-equiv="Pragma" content="no-cache"/>
<META http-equiv="Expires" content="-1"/>
<TITLE>Kiezen op afstand - Databeheer - Scheduler jobs overview</TITLE>
<LINK href="DatabeheerWeb.css" rel="stylesheet" type="text/css">
</HEAD>
<BODY>
<table width="721" border="0" align="center" cellpadding="0" cellspacing="0" valign="middle">
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
<table width="721" border="0" cellspacing="1" cellpadding="4" border="0" align="center">
    <tr>
        <td width="725">
        <form name="search" id="search" action="ScheduledJobsOverview" method="post">
        <fieldset style="border-style: solid; border-width: 1px; border-color: #c2dbf8"><legend class="smallTextalt">[Search]</legend>
        <table width="721" border="0" cellspacing="1" cellpadding="4" border="0">
            <tr>
                <td class="tableBdalt">Job id:</td>
                <td class="tableBdalt"><input type="text" name="jobID" id="jobID" value="<%=overview.getJobID() != null ? overview.getJobID() : "" %>" /></td>
                <td class="tableBdalt">Status:</td>
                <td class="tableBdalt"><select name="status">
                    <option value="All">All</option>
                    <option value="SCHEDULED" <%= overview.getStatus().equals("SCHEDULED") ?  "selected" : ""%>>Scheduled</option>
                    <option value="PROCESSING" <%= overview.getStatus().equals("PROCESSING") ?  "selected" : ""%>>Processing</option>
                    <option value="PROCESSED" <%= overview.getStatus().equals("PROCESSED") ?  "selected" : ""%>>Processed</option>
                    <option value="ABORTED" <%= overview.getStatus().equals("ABORTED") ?  "selected" : ""%>>Aborted</option>
                </select></td>
            </tr>
            <tr>
                <td colspan="4" class="tableBdalt" align="right"><input type="submit" name="submit" id="submit" value="OK"/>&nbsp;</td>
            </tr>
        </table>
        </fieldset>
        </form>
        </td>
    </tr>
</table>

<table width="725" border="0" cellspacing="1" cellpadding="4" border="0" align="center">
<tr><td>Jobs</td></tr>
<% if(!overview.isEmpty())
{
%>
<tr><td><% if (overview.isTruncatedSearch()) { %> Er zijn meer dan <%= SchedulerConstants.MAX_RESULTS %> jobs gevonden, alleen de eerste <%= SchedulerConstants.MAX_RESULTS %> worden getoond. <% } %></td></tr>
</table>
<table width="721" border="0" cellspacing="1" cellpadding="4" bgcolor="#c2dbf8" align="center">
    <tr>
        <td width="50" bgcolor="#c2dbf8" class="tableHd" align="center">Job id</td>
        <td bgcolor="#99a5c0" class="tableHdalt">Type</td>
        <td bgcolor="#99a5c0" class="tableHdalt">Status</td>
        <td bgcolor="#99a5c0" class="tableHdalt" align="center">Start tijd</td>
        <td bgcolor="#99a5c0" class="tableHdalt" align="center">Stop tijd</td>
    </tr>
    <!--== body starts ==-->
    <%
Enumeration enum = overview.getResultSubSet(10, command.getPageNo()-1);
while (enum.hasMoreElements()) {
ScheduledJobDataObject job = (ScheduledJobDataObject)enum.nextElement();
%>
    <tr>
        <td bgcolor="#ffffff" class="tableBd" align="center"><%= job.getJobID() %></td>
        <td bgcolor="#ffffff" class="tableBdalt" align="center"><%=job.getJobTypeName()%></td>
        <td bgcolor="#ffffff" class="tableBdalt" align="center"><%= job.getStatus()%></td>
        <td bgcolor="#ffffff" class="tableBdalt" align="center"><%= new SimpleDateFormat(SchedulerConstants.DATE_TIME_FORMAT).format(job.getStartTime())%></td>
        <td bgcolor="#ffffff" class="tableBdalt" align="center"><%= job.getStopTime() != null ? new SimpleDateFormat(SchedulerConstants.DATE_TIME_FORMAT).format(job.getStopTime()) : ""%></td>
    </tr>
    <%  } %>
</table>

<table width="721" cellspacing="1" cellpadding="4" border="0" align="center">
    <tr>
        <td class="pagecount"><% 
	int pages = (overview.getResultCount()/10);
	if(overview.getResultCount()%10 == 0 && overview.getResultCount()>0) pages--;
	
	if (pages > 1)
	{
		%>Resultaatpagina: <%
		for(int t=1; t<= pages+1; t++)
		{
		%> 
		<a href="ScheduledJobsOverview?page=<%=t%>"><%= t==command.getPageNo()?"<font size=\"2\"><b>"+t+"</b></font>":""+t%></a> 
	<% 
		}
	}%>
		</td>
    </tr>
</table>

<% } else {  // IS EMPTY!!!!! %>
<table width="721" cellspacing="1" cellpadding="4" border="0" align="center">
<tr><td>Geen resultaten gevonden</td></tr>
</table>
<% } %>
<table width="721" align="center">
  <tr>
    <td align="left"><BUTTON STYLE="width:200" ONCLICK="window.location='index.jsp'">Terug naar hoofdpagina</BUTTON>
    </td>
  </tr>
</table>
<table width="721" border="0" align="center" cellpadding="0" cellspacing="0">
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
