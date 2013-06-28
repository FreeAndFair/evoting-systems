<%--
 * Copyright 2006 by Open Voting Solutions Inc
 * 9005 Magruder Knolls Court
 * Gaithersburg,
 * Maryland, 20882
 * USA
 * All rights reserved.
 *
 *
 * $Workfile:: app_footer.jsp                                           $
 * $Author: Chenna Ganesan $
--%>

<%@ page import="java.text.SimpleDateFormat" %>
<%@ page import="java.util.Date" %>
<%@ taglib uri="/WEB-INF/struts-bean.tld" prefix="bean" %>
<%
	SimpleDateFormat formatter = new SimpleDateFormat("MM/dd/yyyy");
	SimpleDateFormat yearOnlyFormat = new SimpleDateFormat("yyyy");
	Date currentTime = new Date();
	String dateString = formatter.format(currentTime);
    String yearString = yearOnlyFormat.format(currentTime);
	String contextPath = request.getContextPath(); 
	String username = (String)session.getAttribute("userID");
%>

<table border="0" cellpadding="2" cellspacing="0" width="100%">
    <tr bgcolor="#FFA042">
      <td><span class="footer"><span class="bold"><font size="2"><bean:message key="todaysdate"/> <%= dateString%></font></span></span></td>
      <td><br>
      </td>
      <td align="right"><span class="footer"><span class="bold"><font size="2"><bean:message key="username"/> <%=username%></font></span></span></td>
    </tr>
</table>


