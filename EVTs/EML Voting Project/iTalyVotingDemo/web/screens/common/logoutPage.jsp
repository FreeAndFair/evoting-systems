<%@ page import="java.text.SimpleDateFormat" %>
<%@ page import="java.util.Date" %>

<%
    SimpleDateFormat formatter;
    formatter = new SimpleDateFormat("MM/dd/yyyy hh:mm:ss a");
    String contextPath = request.getContextPath();
%>
<html>
    <head>
        <meta http-equiv="Expires" content="0">
        <meta http-equiv="Cache-Control" content="no-cache">
        <meta http-equiv="Pragma" content="no-cache">
        <meta http-equiv="content-type" content="text/html;charset=ISO-8859-1">
        <title>Logout!</title>
    </head>
   <STYLE TYPE="text/css">
    <%@ include file="/web/css_files/election.css" %>
  </STYLE>
    <body text="black" link="black" vlink="#ee0000" alink="black">  

  
        <table border="0" cellpadding="0" cellspacing="0" width="100%" height="100%">
            <tr>
                <td align="center" valign="middle">
                    <table width="100%" border="0" name="loginInfo" cellpadding="2" cellspacing="1">
                        <tr>
                            <td colspan="3" align="center">
                                <table width="450" border="0" cellspacing="4" cellpadding="4">
                                    <tr>
                                        <td align="center">
									     <table border="0" cellpadding="0" cellspacing="0">
									            <tr>
									                <td colspan="3" align="center" valign="bottom"><img height="2" width="431" src="<%=contextPath%>/web/images/red_vert_line.gif"></td>
									            </tr>
									            <tr>
									                <td align="right"><img height="17" width="17" src="<%=contextPath%>/web/images/star_gold.gif"></td>
									                <td align="center"><center>
									                   <span class="title_bld_14">Italy Election Management System</scpan></center>
									                </td>
									                <td align="left"><img height="17" width="17" src="<%=contextPath%>/web/images/star_gold.gif"></td>
									            </tr>
									            <tr>
									                <td colspan="3" align="center" valign="top"><img height="2" width="431" src="<%=contextPath%>/web/images/red_vert_line.gif"></td>
									            </tr>
  								         </table>
                                        </td>
                                    </tr>                                  
                                    <tr>
                                        <td><span class="twelvpix">You have been logged off out of Italy Election Management System. Use the link below to re-login to the Italy Election Management System. </span>
                                            <div align="center">
                                                <p><a href="<%=contextPath%>"><span class="twelvpix"><span class="colheadbldforteen">Click here to Login to Italy Election Management System!</span></span></a></p>
                                            </div>
                                        </td>
                                    </tr>
                                </table>
                            </td>
                        </tr>
                        <tr>
                            <td colspan="3" align="right"><br>
                            </td>
                        </tr>                 
                    </table>
                </td>
            </tr>
            <tr height="25">
                <td align="center" valign="bottom" height="25"><!--App Footer Start-->
                    <table border="0" cellpadding="2" cellspacing="0" width="100%">
                        <tr bgcolor="#eb0000">
                            <td align="center">
                            <span class="footer">
                            <span class="bold">
                            <font color="white">Last Modified: <script>
                            	document.write("Last Modified " + document.lastModified)
							</script>
                            </font></span></span></td>
                        </tr>
                    </table>
                    <!--App Footer End--></td>
            </tr>
        </table>
    </body>
</html>

