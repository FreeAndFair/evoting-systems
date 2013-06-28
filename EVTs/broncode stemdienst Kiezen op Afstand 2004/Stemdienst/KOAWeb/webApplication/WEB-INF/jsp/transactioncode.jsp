<%@page import="com.logicacmg.koa.dataobjects.*"%>
<%@page import="com.logicacmg.koa.votecommands.*"%>
<%@page import="com.logicacmg.koa.constants.FunctionalProps"%>
<%
	response.setHeader("Pragma", "no-cache"); //http1.0
	response.setHeader("Cache-Control", "no-cache"); //http1.1
%>
<% 
	VoteCommand xVoteCommand = (VoteCommand)request.getAttribute(CommandConstants.COMMAND_IN_REQUEST_KEY);
	
	
	StemTransactie xStemTransactie = null;
	if(xVoteCommand != null)
	{
		xStemTransactie = xVoteCommand.getStemTransactie();
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
<TITLE>Verkiezing voor de leden van het Europees Parlement 2004 - Ontvangst transactiecode</TITLE>
</HEAD>

<body>


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
                        <td width="200" rowspan="2"><img src="images/orderfull_5_without_transactioncode.gif" width="195" height="120"></td>
	                <%  }
	                    else {
	                %>
                        <td width="200" rowspan="2"><img src="images/orderfull_5.gif" width="195" height="120"></td>
	                <%  } %>
                        <td width="10" rowspan="2"><img src="images/blueline_2.gif" width="2" height="200"></td>
                        
                    <td> <H1>U heeft gestemd</H1>
                        </td>
                    </tr>
                    <tr>
                        
                    <td width="100%" height="230" valign="top"><p>

	                <%
						if( show_transactioncode != null &&
						    show_transactioncode.equalsIgnoreCase("NO") == true )
						{
	                %>
							<table width="100%" border="0" cellpadding="0">
							  <tr> 
         		                <td colspan="2"><font size="2">
		                        <p align="left">Als u opnieuw probeert te stemmen,
		                        zult u het scherm 'u heeft reeds gestemd' te zien
		                        krijgen.</p>
		                        <p align="left">Hartelijk dank voor het uitbrengen
		                        van uw stem.</p>
		                        <p align="left">Om het internetstembureau te
		                        verlaten, sluit u dit scherm.</p></font>&nbsp;</td>
							  </tr>
         		              <tr> 
           		               <td>&nbsp;</td>
             		           <td>&nbsp;</td>
               		          </tr>
                  		    </table>
                  	<%
                  	   }
                  	   else {
                  	%>
							<table width="100%" border="0" cellpadding="0">
       		                  <tr> 
           		                <td width="38%"><font size="2">Uw transactiecode is:</font></td>
			                    <td width="62%"><font size="2"><%= xStemTransactie.Transactienummer%></font></td>
                        	  </tr>
							  <tr> 
         		                <td colspan="2"><font size="2">
         		                Deze transactiecode is
		                        ter bevestiging dat uw stem is opgenomen in de
		                        stembus. Nadat de uitslag van de verkiezing bekend
		                        is gemaakt, wordt een lijst met alle transactiecodes
		                        gepubliceerd.
		                        <p align="left">Als u opnieuw probeert te stemmen,
		                        zult u het scherm 'u heeft reeds gestemd' te zien
		                        krijgen. Als bevestiging van de door u uitgebrachte
		                        stem krijgt u nogmaals de transactiecode te zien.</p>
		                        <p align="left">U kunt eventueel de transactiecode
		                        noteren of deze pagina printen.</p>
		                        <p align="left">Hartelijk dank voor het uitbrengen
		                        van uw stem.</p>
		                        <p align="left">Om het internetstembureau te
		                        verlaten, sluit u dit scherm.</p></font>&nbsp;</td>
							  </tr>
                  		    </table>
					<% } %>                  	
                    </tr>
                </table>
                <table width="100%" border="0" cellpadding="3">
                    <tr>
                        <td width="133" height="38"><img src="images/filler.gif" width="218" height="1"></td>
                        <td height="38">&nbsp;</td>
                        <td height="38">
                        <div align="right"></div>
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


</body>

<%
	try
	{
		session.invalidate();
	}
	catch (IllegalStateException ise)
	{
		//session is already invalidated
	}

%>

<HEAD>
<META http-equiv="Pragma" content="no-cache"/>
<META http-equiv="Expires" content="-1"/>
</HEAD>
</HTML>
