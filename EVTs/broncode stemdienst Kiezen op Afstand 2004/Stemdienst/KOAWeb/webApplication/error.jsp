<%@page import="com.logicacmg.koa.votecommands.CommandConstants"%>
<%
	response.setHeader("Pragma", "no-cache"); //http1.0
	response.setHeader("Cache-Control", "no-cache"); //http1.1
%>
<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN">
<HTML>
<HEAD>
<META name="GENERATOR" content="IBM WebSphere Studio">
<META http-equiv="Pragma" content="no-cache"/>
<META http-equiv="Expires" content="-1"/>
<TITLE>Verkiezing voor de leden van het Europees Parlement 2004 - Foutpagina</TITLE>
<LINK href="KiezerWeb.css" rel="stylesheet" type="text/css">
</HEAD>
<BODY>
<table width="725" border="0" align="center" cellpadding="0" cellspacing="0">
    <tr>
        <td colspan="3"> <div align="left">             <table width="100%" border="0" cellspacing="0" cellpadding="0">
                <tr>
            <td width="640" bgcolor="#6699CC" height="57">
<div align="center"><font color="#FFFFFF" size="4" face="Arial, Helvetica, sans-serif"><strong>Verkiezing van de leden van het Europees Parlement 2004
                </strong></font></div></td>
                </tr>
              </table></div></td>
    </tr>
    <tr valign="top">
        <td width="3%" align="left"><img src="images/blueline_3.gif" width="1" height="380"></td>
        <td width="94%" valign="top">
        <div align="center">&nbsp;
        <table width="100%" border="0" cellpadding="3">
            <tr>
                <td align="left">
                <p><H3><%= request.getAttribute(CommandConstants.ERROR_IN_REQUEST_KEY) %></H3></p>
                </td>
            </tr>
        </table>
        <table width="100%" border="0" cellpadding="3">
            <tr>
                <td width="133"><img src="images/filler.gif" width="218" height="1"></td>
                <td>&nbsp;</td>
                <td>
                <div align="right"><a href=""><img src="images/verder_3.gif" width="108" height="46" border="0"></a></div>
                </td>
            </tr>
        </table>
        </div>
        </td>
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
</BODY>
<HEAD>
<META http-equiv="Pragma" content="no-cache"/>
<META http-equiv="Expires" content="-1"/>
</HEAD>
</HTML>
