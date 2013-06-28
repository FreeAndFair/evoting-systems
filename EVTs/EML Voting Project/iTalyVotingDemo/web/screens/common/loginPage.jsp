<%@ taglib uri="/WEB-INF/struts-bean.tld" prefix="bean" %>
<%@ taglib uri="/WEB-INF/struts-html.tld" prefix="html" %>
<%@ taglib uri="/WEB-INF/struts-logic.tld" prefix="logic" %>
<%@ taglib uri="/WEB-INF/struts-tiles.tld" prefix="tiles" %>
<%@ page import="org.apache.struts.action.ActionMessages" %>
<%@ page import="java.util.*" %>

<%
    // This variable will be equal to the URL pattern of the web application server.
    String contextPath = request.getContextPath();
    String remoteUser = null;
    remoteUser = request.getRemoteUser();
%>
  <STYLE TYPE="text/css">
    <%@ include file="/web/css_files/election.css" %>
  </STYLE>

<table border="0" cellpadding="0" cellspacing="0" width="100%" height="98%">
    <tr><td align="center" valign="middle">
        <table border="0" cellpadding="0" cellspacing="0">
            <tr>
                <td colspan="3" align="center" valign="bottom"><img height="2" width="431" src="<%=contextPath%>/web/images/red_vert_line.gif"></td>
            </tr>
            <tr>
                <td align="right"><img height="17" width="17" src="<%=contextPath%>/web/images/star_gold.gif"></td>
                <td align="center"><center>
                   <span class="title_bld_14">Italy Election System</scpan></center>
                </td>
                <td align="left"><img height="17" width="17" src="<%=contextPath%>/web/images/star_gold.gif"></td>
            </tr>
            <tr>
                <td colspan="3" align="center" valign="top"><img height="2" width="431" src="<%=contextPath%>/web/images/red_vert_line.gif"></td>
            </tr>
        </table>
        <table border="0" cellpadding="0" cellspacing="0" width="507" height="402">
            <tr>
                <td>
                    <html:form action="/actions/login" >
                        <table width="100%" border="0" name="loginInfo" cellpadding="2" cellspacing="1">
                          <tr>
                            <td width="51%" class="col_head_bld_12">
                              <div align="right" class="col_head_bld_12"><bean:message key="username"/></div>
                            </td>
                            <td width="49%">
                              <html:text property="userID"  tabindex="1" />
                            </td>
                          </tr>
                          <tr>
                            <td width="51%">
                              <div align="right" class="col_head_bld_12"><bean:message key="password"/></div>
                            </td>
                            <td width="49%">
                              <html:password property="password"  tabindex="2"/>
                            </td>
                          </tr>
                          <tr><br>
                            <td COLSPAN="2" width="51%" align="center">
	                            <center>                          
	                                <input type="submit" name="Login" value="Login" class="epbButton"">
	                            </center>
                            </td>
                            <td width="49%">&nbsp;</td>
                          </tr>
                        </table>  
                         <center><div id="message" class="message">
                         <logic:present name="messageBean">
                         <font color=red><bean:write name="messageBean" property="message"/></font>
                         </logic:present>
                         </div></center>
                    </html:form>                  
                </td>
            </tr>
        </table>
    </td></tr>
</table>