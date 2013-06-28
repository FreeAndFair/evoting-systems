<%--
 * Copyright 2006 by Open Voting Solutions Inc
 * 9005 Magruder Knolls Court
 * Gaithersburg,
 * Maryland, 20882
 * USA
 * All rights reserved.
 *
 *
 * $Workfile:: epbBanner.jsp                                           $
 * $Author: Chenna Ganesan $
--%>

<%@ taglib uri="/WEB-INF/struts-bean.tld" prefix="bean" %>
<%   
    String mainURLPattern = this.getServletConfig().getServletContext().getInitParameter("main.url.pattern");
    String contextPath = request.getContextPath();   
    String username = (String)session.getAttribute("userID");
%>

  <table border="0" cellpadding="0" cellspacing="8" width="100%">	
    <tr>
        <td nowrap valign="middle"><font size="2"><b>
            <img src="<%=contextPath%>/web/images/flag.jpg" border="0" alt="Election System">
            Connecticut Election System</b></font>
        </td>

        <td align="center" nowrap valign="middle" width="395"><font size="2">

          </font>
         <table border="0" cellspacing="2" cellpadding="0">
            <tr>
              <td nowrap><span class="app_head"><tiles:insert attribute="HtmlTitle" /></span><br>
                         <span class="app_note"><tiles:insert attribute="ScreenDesc" /></span></td>
            </tr>
          </table>
        <font size="2">

        </font></td>

        <td valign="middle" align="right">
          <span class="12_px">
            <a href="<%=contextPath%>/homePage.do"><font color="black"><nobr><bean:message key="mainmenu"/> </nobr></font></a><nobr><br></nobr>
          </span><font size="2"><span class="12_px"><nobr></nobr></span></font>
        </td>

        <td valign="middle" width="47">
            <a href="<%=contextPath%>/actions/login.do?pageAction=logout"><img src="<%=request.getContextPath()%>/web/images/logout.gif" width="47" height="31" border="0" alt="<bean:message key="logout"/> <%=username%>" align="right"></a>
        </td>

        <td valign="middle" width="35">
            <a href="<%=contextPath%>/scanVoter.do?pageAction=defaultPage"><img src="<%=request.getContextPath()%>/web/images/home_btn.gif" width="35" height="31" border="0" alt="portal"></a>
        </td>

    </tr>
   </table>




