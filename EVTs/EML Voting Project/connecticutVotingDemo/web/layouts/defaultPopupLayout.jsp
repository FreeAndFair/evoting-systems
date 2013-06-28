<%--
                                $
 *  $Author: chennag $
--%>

<%@ taglib uri="/WEB-INF/struts-tiles.tld" prefix="tiles"%>

<html>
 <head>
   <title><tiles:insert attribute="HtmlTitle" /></title>
   <meta http-equiv="content-type" content="text/html;charset=ISO-8859-1">
 </head>
   <STYLE TYPE="text/css">
    <%@ include file="/web/css_files/election.css" %>
  </STYLE>

 <body topmargin="0" leftmargin="0" bgcolor="#FFFFFF">
 <table align="center">
   <tr>
     <td align="center">
       <!-- Main body information -->
       <%@ include file="/web/screens/common/loginPage.jsp" %>
     </td>
   </tr>
   <tr>
     <td align="center">
       <!-- AppFooter information -->
       <%@ include file="/web/screens/common/footer.jsp" %>
     </td>
   </tr>
 </table>
 </body>
</html>
