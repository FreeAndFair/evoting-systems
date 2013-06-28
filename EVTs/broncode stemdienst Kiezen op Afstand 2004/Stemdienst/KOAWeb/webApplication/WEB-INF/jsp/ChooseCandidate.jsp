<%@page import="com.logicacmg.koa.constants.FunctionalProps"%>
<%@page import="com.logicacmg.koa.votecommands.*" contentType="text/html; charset=UTF-8" %>
<%
	response.setHeader("Pragma", "no-cache"); //http1.0
	response.setHeader("Cache-Control", "no-cache"); //http1.1
%>
<% 
   VerifyCandidateCommand xCommand = null;
   
   Object xObject = request.getAttribute(CommandConstants.COMMAND_IN_REQUEST_KEY);
   if(xObject != null)
   {
   	  
   	  if(xObject instanceof com.logicacmg.koa.votecommands.VerifyCandidateCommand)
   	  {
         xCommand = (VerifyCandidateCommand) xObject;
      }
   } 
%>
<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN">
<HTML>
<HEAD>
<META http-equiv="Content-Style-Type" content="text/css">
<META name="GENERATOR" content="IBM WebSphere Studio">
<META http-equiv="Pragma" content="no-cache"/>
<META http-equiv="Expires" content="-1"/>
<LINK href="KiezerWeb.css" rel="stylesheet" type="text/css">
<TITLE>Verkiezing voor de leden van het Europees Parlement 2004 - Kiezen kandidaat</TITLE>
</HEAD>

<body>
<FORM method="post" action="KandidaatKeuze">

        <table width="725" border="0" align="center" cellpadding="0" cellspacing="0">
            <tr>
                <td colspan="3">              <table width="100%" border="0" cellspacing="0" cellpadding="0">
                <tr>
                  <td width="640" height="57" bgcolor="#6699CC">
<div align="center"><font color="#FFFFFF" size="4" face="Arial, Helvetica, sans-serif"><strong>Verkiezing van de leden van het Europees Parlement 2004 
                      </strong></font></div></td>
                </tr>
              </table></td>
            </tr>
            <tr valign="top">
                <td width="3%" align="left"><img src="images/blueline_3.gif" width="1" height="380"></td>
                <td width="94%" valign="top">
                <div align="center"><br>
                <table width="100%" border="0" cellpadding="3" height="267">
                    <tr>
	                <%
						String show_transactioncode = FunctionalProps.getProperty(FunctionalProps.SHOW_TRANSACTIONCODE);
						if( show_transactioncode != null &&
						    show_transactioncode.equalsIgnoreCase("NO") == true )
						{
	                %>
                        <td width="200" rowspan="2"><img src="images/orderfull_2_without_transactioncode.gif" width="195" height="120"></td>
	                <%  }
	                    else {
	                %>
                        <td width="200" rowspan="2"><img src="images/orderfull_2.gif" width="195" height="120"></td>
	                <%  } %>
                        <td width="10" rowspan="2"><img src="images/blueline_2.gif" width="2" height="200"></td>
                        <td>
                        <H1>Kiezen kandidaat</H1>
                        </td>
                    </tr>
                    <tr>
                        
                    <td width="100%" height="230" valign="top"> 

                      <p><font size="2">Voer de negen-cijferige kandidaatcode 
                        van de kandidaat van uw keuze in. De kandidaatcodes zijn 
                        vermeld bij de kandidaten op het overzicht van kandidatenlijsten 
                        dat aan u is toegezonden.</font></p>
                      <table width="100%" border="0" cellpadding="5">
                        <tr> 
                          <td width="27%"><font size="2">Kandidaatcode:</font></td>
                          <td width="73%">
                                <input name="KANDIDAATCODE1" type="text" maxlength="3" size="4">
                                <input name="KANDIDAATCODE2" type="text" maxlength="3" size="4">
                               	<input name="KANDIDAATCODE3" type="text" maxlength="3" size="4">
                          </td>
                        </tr>
                      </table>
                        <P><%  String sMessage = null;
                                
                                	if(xCommand != null)
                                	{
                                	   sMessage = xCommand.getValidationMessage();
                                	}

                                    if(sMessage != null && sMessage.trim().length() > 0)
                                    { %>
                        <H3><%= sMessage%></H3>
                        <%}
                                    else
                                    {%> &nbsp; <%}%>
                        </td>
                    </tr>
                </table>
                <table width="100%" border="0" cellpadding="3">
                    <tr>
                        <td width="173" height="38"><a href="identification.jsp"><img src="images/terug_2.gif" width="108" height="46" border="0" alt="druk hierop om terug te gaan naar de eerste pagina"></a></td>
                        <td height="38">&nbsp;</td>
                        <td height="38">
                        <div align="right"><input type="image" src="images/verder_3.gif" width="108" height="46" border="0" alt="druk op verder om te kunnen stemmen"></div>
                        </td>
                    </tr>
                </table>
                </div>
                <td width="3%" align="right"><img src="images/blueline_3.gif" width="1" height="380"></td>
            </tr>
            <tr valign="top">
                <td height="1" colspan="3"><img src="images/horizontalline_2.gif" width="726" height="1"></td>
            </tr>
            <tr valign="top">
                <td colspan="3">
                <div align="center">
                <H2>De verantwoordelijkheid voor deze site berust bij het ministerie van Binnenlandse Zaken en Koninkrijksrelaties</H2>
                </div>
                </td>
            </tr>
        </table>

</form>
</body>
<HEAD>
<META http-equiv="Pragma" content="no-cache"/>
<META http-equiv="Expires" content="-1"/>
</HEAD>
</HTML>
