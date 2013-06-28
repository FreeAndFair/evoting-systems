<%@ taglib uri="/WEB-INF/struts-bean.tld" prefix="bean" %>
<%@ taglib uri="/WEB-INF/struts-html.tld" prefix="html" %>
<%@ taglib uri="/WEB-INF/struts-logic.tld" prefix="logic" %>
<%@ taglib uri="/WEB-INF/struts-tiles.tld" prefix="tiles" %>
<%@ page import="org.apache.struts.action.ActionMessages" %>
<%@ page import="java.util.*" %>

<%
    // This variable will be equal to the URL pattern of the web application server.
    String contextPath = request.getContextPath();   
%>
<SCRIPT LANGUAGE=JAVASCRIPT TYPE="TEXT/JAVASCRIPT">
<!--Hide script from old browsers

function newWindow(newContent)
 {
  winContent = window.open(newContent, 'nextWin', 'right=0, top=20,width=350,height=350, toolbar=yes,scrollbars=yes, resizable=yes')         
 }

 //Stop hiding script from old browsers -->
 </SCRIPT>

   <form method="post" name="voterForm" action="<%=request.getContextPath()%>/scanVoter.do" >
   <center>
    <table border="0" cellpadding="0" cellspacing="0">
     <tr>
      <td>
       Bar Code is Valid...
      </td>
      </tr>
      <tr>
      <td> 
	<INPUT type="button" value="Start Voting!" onClick="window.open('http://odganesanwxp:8080/ItalyVoting/web/screens/voter/ItalianSenateBallot/voting_ballot.xml','ballotwindow','width=825,height=550,left=0,top=100,screenX=0,screenY=100,location=yes')"> 
      </td> 
     </tr>
    </table>  
   </center>
   </form> 