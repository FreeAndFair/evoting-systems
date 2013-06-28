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
 <script language="JavaScript1.2">

  function loadCountingPage() {
    var cType="";
    cType=document.forms[0].countingType.value;
    if(cType=="") {
      document.forms[0].eml440To510.disabled=true;
      document.forms[0].eml510To520.disabled=true;
    }
    if(cType=="ballotToEML440") {
      document.forms[0].eml440To510.disabled=true;
      document.forms[0].eml510To520.disabled=true;
    }
     if(cType=="eml440To510") {
      document.forms[0].ballotToEML440.disabled=true;
      document.forms[0].eml510To520.disabled=true;
    }
     if(cType=="eml510To520") {
      document.forms[0].ballotToEML440.disabled=true;
      document.forms[0].eml440To510.disabled=true;
    }
     if(cType=="done") {
      document.forms[0].ballotToEML440.disabled=true;
      document.forms[0].eml440To510.disabled=true;
       document.forms[0].eml510To520.disabled=true;
    }
   }
 function setCountingType(cType){
    document.forms[0].countingType.value=cType;
    document.forms[0].submit();
 }
</script>
<body onload="loadCountingPage()">
   <html:form action="/actions/counting" >
   <center>
    <br><br>
    <logic:present name="messageBean">
           <font color=green><b><bean:write name="messageBean" property="message"/></b></font>
    </logic:present>
    <br><br>
     <table border="0" cellpadding="0" cellspacing="0">
     <tr>
      <td>
       <input type="button" name="ballotToEML440" value="Ballot To EML440" class="counting_btns" onclick="setCountingType('ballotToEML440')">
      </td>
     </tr>
     <tr>
      <td>
       <input type="button" name="eml440To510" value="EML440 To EML510" class="counting_btns" onclick="setCountingType('eml440To510')">
      </td>
     </tr>
     <tr>
      <td>
       <input type="button" name="eml510To520" value="EML510 To EML520" class="counting_btns" onclick="setCountingType('eml510To520')">
      </td>
     </tr>
    </table>
    <br><br>
   <logic:equal parameter="countingType" value="done">
     <font color="9acd32"><b>
      <a href="http://openvotingsolutions.info/connecticutVotingDemo/xml/eml520result/EML520_Result.xml">
      Please click here to view the EML 510 result</a>				
     </font>
   </logic:equal>
   </center>
   <html:hidden property="countingType" />
  </html:form>
  </body>
