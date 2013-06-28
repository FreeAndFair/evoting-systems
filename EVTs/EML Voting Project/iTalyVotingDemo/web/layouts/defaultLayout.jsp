<%--
 * Copyright 2006 by Open Voting Solutions Inc
 * 9005 Magruder Knolls Court
 * Gaithersburg,
 * Maryland, 20882
 * USA
 * All rights reserved.
 *
 *
 * $Workfile:: epbDefaultLayout.jsp                                           $
 * $Author: Chenna Ganesan $
--%>

<%@ taglib uri="/WEB-INF/struts-bean.tld" prefix="bean" %>
<%@ taglib uri="/WEB-INF/struts-html.tld" prefix="html" %>
<%@ taglib uri="/WEB-INF/struts-tiles.tld" prefix="tiles" %>

<% 
    String applicationName = "E-PollBooks";
    //this.getServletConfig().getServletContext().getInitParameter("applicationName");
%>

<html:html>
  <head>
    <title>
      <tiles:insert attribute="HtmlTitle"/>
    </title>
    <meta http-equiv="content-type" content="text/xml;charset=ISO-8859-1">
  </head>
  <STYLE TYPE="text/css">
    <%@ include file="/web/css_files/election.css" %>
  </STYLE>

  <body bgcolor="white">
    <%@ include file="/web/screens/common/banner.jsp" %> <%-- This is intentionally a static include! --%>
        <tiles:insert attribute="HtmlMenu"/>
        <table width="100%"><tr><td>
        <%@ include file="/web/screens/common/note.jsp" %> 
        
        <br><br>        
        <table width="100%"><tr><td>
                <tiles:insert attribute="HtmlBody"/>
          </td></tr>
          <tr><td>&nbsp;</td></tr>
          <tr><td>&nbsp;</td></tr>
        </table>
        
        <!-- check for user validaton -->
        <!--
        <table width="100%"><tr><td>
                You do not have access to the application.  Please contact the ServiceDesk to request access.
          </td></tr>
          <tr><td>&nbsp;</td></tr>
          <tr><td>&nbsp;</td></tr>
        </table>
        -->
        
    <tiles:insert attribute="AppFooter" />
    <tiles:insert attribute="HtmlFooter"/>
    </td></tr></table>
  </body>

</html:html>

