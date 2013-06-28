<%@page import="com.logicacmg.koa.dataobjects.*,com.logicacmg.koa.votecommands.*" contentType="text/html; charset=UTF-8"%>
<%@page import="com.logicacmg.koa.constants.FunctionalProps"%>

<%

	response.setHeader("Pragma", "no-cache"); //http1.0

	response.setHeader("Cache-Control", "no-cache"); //http1.1

%>

<%

	VerifyCandidateCommand xCommand = (VerifyCandidateCommand)request.getAttribute(CommandConstants.COMMAND_IN_REQUEST_KEY);

	

	KandidaatResponse xKandidaatResponse = null;

	

	if(xCommand != null)

	{

		xKandidaatResponse = xCommand.getKandidaatResponse();

	}

	

	Kandidaat xKandidaat = null;

	

	if(xKandidaatResponse != null)

	{

		xKandidaat = xKandidaatResponse.kandidaat;

	}

	

	String sName = null;



	if(xKandidaat != null)

	{

	   sName = xKandidaat.voorletters;

	   

	   if(xKandidaat.roepNaam != null && xKandidaat.roepNaam.trim().length() > 0)

	   {

	      sName= sName + " (" + xKandidaat.roepNaam + ")";

	   }

	   

	   if(xKandidaat.geslacht != ' ')

	   {

	      sName = sName + " (" + xKandidaat.geslacht + ")";

	   }

	}



%>

<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN">

<HTML>

<script language="javascript">

function submitForm(action) {

   document.commitcandidate.nav.value=action;

   document.commitcandidate.submit();

}

</script>

<HEAD>

<META http-equiv="Content-Style-Type" content="text/css">

<META name="GENERATOR" content="IBM WebSphere Studio">

<META http-equiv="Pragma" content="no-cache"/>

<META http-equiv="Expires" content="-1"/>

<LINK href="KiezerWeb.css" rel="stylesheet" type="text/css">

<TITLE>Verkiezing voor de leden van het Europees Parlement 2004 - Bevestigen kandidaat</TITLE>

</HEAD>



<body>

<form name="commitcandidate" method="POST" action="BevestigKeuze"><input type="hidden" name="nav">



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
                        <td width="200" rowspan="2"><img src="images/orderfull_3_without_transactioncode.gif" width="195" height="120"></td>
	                <%  }
	                    else {
	                %>
                        <td width="200" rowspan="2"><img src="images/orderfull_3.gif" width="195" height="120"></td>
	                <%  } %>

                        <td width="10" rowspan="2"><img src="images/blueline_2.gif" width="2" height="200"></td>

                        

                    <td> <H1>Bevestigen kandidaatkeuze</H1>

                        </td>

                    </tr>

                    <tr>

                        

                    <td width="100%" height="230" valign="top"> 

                      <table width="100%" border="0" cellpadding="5">

                        <tr> 

                          <td width="38%"><font size="2">U heeft ingevoerd kandidaatcode:</font></td>

                          

                    <td width="62%" valign="bottom"><strong><%= xKandidaatResponse.kandidaatcode%></strong></td>

                        </tr>

                        <tr> 

<%

	if (xCommand.isBlankCandidate()) {

%>                        

                          <td valign="top"><font size="2">&nbsp;</font></td>

                          <td><table width="100%" border="0" cellspacing="0" cellpadding="0">

                              <tr> 

                                <td colspan="2"><font size="2"><strong><%=FunctionalProps.getProperty(FunctionalProps.BLANK_VOTE_TEXT)%><strong></font></td>

                                

                                                        

                          <td>&nbsp;</td>

                              </tr>

                              <tr> 

                                <td valign="top"><font size="2">&nbsp;</font></td>

                                

                          <td width="9%" valign="top">&nbsp;</td>

                                <td width="61%"><p>&nbsp;<BR>

                              &nbsp;<BR>

                              &nbsp;</p></td>

                              </tr>

                            </table></td>

<%

	} else {

%>                          

                          <td valign="top"><font size="2">Deze kandidaatcode hoort bij:</font></td>

                          <td valign="top"><table width="100%" border="0" cellpadding="0" cellspacing="0">

                              <tr valign="top"> 

                                <td width="30%" valign="top"><font size="2">Lijst:</font></td>

                                

                          <td valign="top"><%= xKandidaat.kieslijstnummer%></td>

                                

                          <td valign="top"><%= xKandidaat.lijstnaam%></td>

                              </tr>

                              <tr> 

                                <td valign="top"><font size="2">Kandidaat:</font></td>

                                

                          <td width="9%" valign="top"><%= xKandidaat.positienummer%></td>

                                <td width="61%"><p><%= xKandidaat.achterNaam%>,<BR>

                              <%= sName%><BR>

                              <%= xKandidaat.woonplaats%></p></td>

                              </tr>

                            </table></td>

<%

	}

%>                            

                        </tr>

                        <tr><td colspan="2">&nbsp;</td></tr>
                        <tr> 

                          <td colspan="2"><p><font size="2">Wilt u uw keuze nog 

                              wijzigen, klik dan op TERUG.</font></p>

                            <p><font size="2">Klik op BEVESTIG om uw keuze definitief 

                              uit te brengen.</font></p></td>

                        </tr>

                      </table>

                        



                        </td>

                    </tr>

                </table>

                <table width="100%" border="0" cellpadding="3">

                    <tr>

                        <td width="133" height="38"><img src="images/filler.gif" width="218" height="1"></td>

                        

                    

              <td width="173" height="38"><a href="javascript:submitForm('PREVIOUS')"><img src="images/terug_2.gif" width="108" height="46" border="0" alt="druk hierop om terug te gaan naar de kandidaat selectie"></a></td>

                        

              <td width="265" height="38"> 

                <div align="right"> 

                  <a href="javascript:submitForm('BEVESTIG')"><img src="images/bevestig.gif" width="108" height="46" border="0" alt="druk op deze knop om uw keuze te bevestigen"></a>

                      </div>

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

