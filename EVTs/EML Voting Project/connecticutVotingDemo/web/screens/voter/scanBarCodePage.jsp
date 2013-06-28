<%@ taglib uri="/WEB-INF/struts-bean.tld" prefix="bean" %>
<%@ taglib uri="/WEB-INF/struts-html.tld" prefix="html" %>
<%@ taglib uri="/WEB-INF/struts-logic.tld" prefix="logic" %>
<%@ taglib uri="/WEB-INF/struts-tiles.tld" prefix="tiles" %>
<%@ page import="org.apache.struts.action.ActionMessages" %>
<%@ page import="java.util.*" %>
<%@ page import="java.io.*" %>
<%
    // This variable will be equal to the URL pattern of the web application server.
    String contextPath = request.getContextPath();   
%>
   <html:form action="/actions/scanvoter.do" >
   <center>
    <table border="0" cellpadding="0" cellspacing="0">
     <tr>
      <td>      
       <bean:message key="barcode"/><html:text property="barCode"  tabindex="1"/>
      </td>
      <td> 
       <input type=hidden name=pageAction value="barcode">
       <input type="submit" name="voterForm" value="Go" class="app_btns">
      </td> 
     </tr>
    </table>  
   </center>
  </html:form>   