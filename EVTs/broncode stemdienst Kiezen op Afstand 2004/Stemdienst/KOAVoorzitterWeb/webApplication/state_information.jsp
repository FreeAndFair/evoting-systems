<%@page import="java.util.*" %>
<%@page import="com.logicacmg.koa.constants.*" %>
<%@page import="com.logicacmg.koa.voorzitter.command.*" %>
<%@page import="com.logicacmg.koa.voorzitter.command.statechange.*" %>
<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN">
<HTML>
<HEAD>
<META name="GENERATOR" content="IBM WebSphere Studio">
<META http-equiv="Pragma" content="no-cache"/>
<META http-equiv="Expires" content="-1"/>
<TITLE>Kiezen op afstand - Voorzitter - Status wijzigen</TITLE>
<LINK href="VoorzitterWeb.css" rel="stylesheet" type="text/css">

<SCRIPT LANGUAGE="Javascript" type="text/javascript">

	function setPinCodes(form)
	{
		form.pincode1.value = document.pincode_form.pincode1.value;
		form.pincode2.value = document.pincode_form.pincode2.value;
		if (confirm('Weet u zeker dat u de status wilt wijzigen?'))
			return true;
		else
			return false;
	}

</SCRIPT>

</HEAD>
<%
	GetCurrentStateCommand command = 
		(GetCurrentStateCommand) request.getAttribute(CommandConstants.COMMAND_IN_REQUEST_KEY);
	
	String sCurrentState = command.getCurrentState();
	Vector vValidStateChanges = command.getValidStateChanges();
	Enumeration enum = vValidStateChanges.elements();
%>
<BODY>
<table width="725" border="0" align="center" cellpadding="0" cellspacing="0">
  <tr>
	<td colspan="3" background="images/banner_filler.gif"><div align="left">
		<table width="100%" border="0" cellspacing="0" cellpadding="0">
		<tr>
			<td width="76" height="57">
				<div align="left"><IMG src="images/leeuw.gif" width="76" height="57" border="0"></div>
			</td>
			<td width="640" height="57">
				<div align="center"><font color="#FFFFFF" size="4" face="Arial, Helvetica, sans-serif">
					<strong>Verkiezing van de leden van het Europees Parlement 2004</strong></font>
				</div>
			</td>
		</tr>
		</table>
	</div></td>  
  </tr>
  <tr valign="top">
    <td width="3%" align="left" height="380"><img src="images/blueline_3.gif" width="1" height="550"></td>
    <td width="94%" valign="top" height="360">
    <br>
    Op deze pagina kan de status van de stemdienst gewijzigd worden.<BR>
    De huidige status is: <b><%= SystemState.getDutchTranslationForState (sCurrentState) %></b><BR><BR>

    Voordat een statuswijziging kan worden doorgevoerd dienen de voorzitter en &eacute;&eacute;n lid van het stembureau hieronder hun pincode in te vullen:
    <FORM NAME="pincode_form" METHOD="POST">
    <TABLE border="0" width="100%">
      <TR>
        <TD>pincode voorzitter van het stembureau: <input type="password" name="pincode1" maxlength="5"></TD>
        <TD>pincode lid stembureau: <input type="password" name="pincode2" maxlength="5"></TD>
      </TR>
    </TABLE>
    </FORM>

    Mogelijke statuswijzigingen zijn:
    <%
      while (enum.hasMoreElements())
      { 
        String sAvailableState = (String) enum.nextElement();
			
        if (sAvailableState.equals (SystemState.INITIALIZED)) {
     %>
      
    <FORM name="initialize_form" action="ChangeStateInitialize" method="POST" enctype="multipart/form-data" onsubmit="return setPinCodes(document.initialize_form)">
    <input type="hidden" name="pincode1">
    <input type="hidden" name="pincode2">					
    <TABLE border="0" width="100%">
      <TR><TD colspan="2"><b>Initialiseren Stemming</b></TD></TR>        					
      <TR bgcolor="#CCCCCC"><TD width="100%" colspan="2"><img src="images/filler.gif" width="1" height="1"></TD></TR>
      <TR><TD colspan="2">Voer uw wachtwoord en de lokatie van het bestand met uw public key in om de stemming te initialiseren.</TD></TR>
      <TR><TD><BR></TD><TD><BR></TD></TR>        
      <TR><TD>Public Key file</TD><TD><INPUT type="file" name="<%= InitializeCommand.PUBLIC_KEY_NAME %>"></TD></TR>
      <TR><TD>Wachtwoord</TD><TD><input type="password" name="<%= InitializeCommand.PASSWORD_NAME %>"></TD></TR>        
      <TR><TD><BR></TD><TD><BR></TD></TR>        
      <TR><TD></TD><TD align="right"><input name="submit" value="Initialiseren Stemming" type="submit" alt="druk op verder om het systeem te initialiseren"></TD></TR>
      <TR bgcolor="#CCCCCC"><TD colspan="2" width="100%"><img src="images/filler.gif" width="1" height="1"></TD></TR>
    </TABLE>
    </FORM>
    <%			
       } else if (sAvailableState.equals(SystemState.OPEN)) {
    %>
    <FORM name="open_form" action="ChangeStateOpen" method="POST" onsubmit="return setPinCodes(document.open_form)">
    <input type="hidden" name="pincode1">
    <input type="hidden" name="pincode2">					
    <%
      String sMessage = "Open stemming";
      String sTooltip = "openen";
      if (sCurrentState.equals (SystemState.RE_INITIALIZED))
      {
        sTooltip = "hervatten";
        sMessage = "Stemming hervatten";
      } 
    %>
    <TABLE border="0" width="100%">
      <TR><TD><b><%= sMessage %></b></TD></TR>        					
      <TR bgcolor="#CCCCCC"><TD width="100%"><img src="images/filler.gif" width="1" height="1"></TD></TR>
      <TR>
        <TD><%= sMessage %>. Na deze actie kan er gestemd worden.</TD>
      </TR>					        	
      <TR>					        	
        <TD align="right"><input type="submit" name="submit" value="<%= sMessage %>" alt="druk op verder om de verkiezing te <%= sTooltip %>"></TD>
      </TR>
      <TR bgcolor="#CCCCCC"><TD width="100%"><img src="images/filler.gif" width="1" height="1"></TD></TR>					        
    </TABLE>
    </FORM>
    <%
      } else if (sAvailableState.equals(SystemState.CLOSED)) {
    %>
    <FORM name="close_form" action="ChangeStateClose" method="POST" onsubmit="return setPinCodes(document.close_form)">
    <input type="hidden" name="pincode1">
    <input type="hidden" name="pincode2">					
    <TABLE border="0" width="100%">
      <TR><TD><b>Sluiten Stemming</b></TD></TR>        					
      <TR bgcolor="#CCCCCC"><TD width="100%"><img src="images/filler.gif" width="1" height="1"></TD></TR>
      <TR>
        <TD>Sluiten Stemming. Na deze actie is het niet meer mogelijk te stemmen.</TD>
      </TR>					        	
      <TR>					        	
        <TD align="right"><input type="submit" name="submit" value="Sluiten Stemming" alt="druk op verder om de verkiezing te sluiten"></TD>
      </TR>
      <TR bgcolor="#CCCCCC"><TD width="100%"><img src="images/filler.gif" width="1" height="1"></TD></TR>					        
    </TABLE>
    </FORM>

	<%
			} else if (sAvailableState.equals(SystemState.RE_INITIALIZED)) {
	%>
	<FORM name="re_initialize_form" action="ChangeStateReInitialize" method="POST" enctype="multipart/form-data" onsubmit="return setPinCodes(document.re_initialize_form)">
	<input type="hidden" name="pincode1">
	<input type="hidden" name="pincode2">					
	<TABLE border="0" width="100%">
	        <TR><TD colspan="2"><b>Herinitialiseren Stemming</b></TD></TR>        					
			<TR bgcolor="#CCCCCC"><TD colspan="2" width="100%"><img src="images/filler.gif" width="1" height="1"></TD></TR>
			<TR><TD colspan="2">Voer uw wachtwoord en de lokatie van het bestand met uw public key in om de stemming te herinitialiseren.</TD><TD></TD></TR>
	        <TR><TD><BR></TD><TD><BR></TD></TR>        
	        <TR><TD>Public Key file</TD><TD><INPUT type="file" name="<%= ReInitializeCommand.PUBLIC_KEY_NAME %>"></TD></TR>
	        <TR><TD>Wachtwoord</TD><TD><input type="password" name="<%= ReInitializeCommand.PASSWORD_NAME %>"></TD></TR>        
	        <TR><TD><BR></TD><TD><BR></TD></TR>        
	        <TR><TD></TD><TD align="right"><input name="submit" value="Herinitialiseren stemming" type="submit" alt="druk op verder om het systeem te herinitialiseren"></TD></TR>
			<TR bgcolor="#CCCCCC"><TD colspan="2" width="100%"><img src="images/filler.gif" width="1" height="1"></TD></TR>
	</TABLE>
	</FORM>		
	<%
			} else if (sAvailableState.equals(SystemState.SUSPENDED)) {
	%>
	<FORM name="suspend_form" action="ChangeStateSuspend" method="POST" onsubmit="return setPinCodes(document.suspend_form)">
	<input type="hidden" name="pincode1">
	<input type="hidden" name="pincode2">					
	<TABLE border="0" width="100%">
	        <TR><TD><b>Onderbreken Stemming</b></TD></TR>        					
			<TR bgcolor="#CCCCCC"><TD width="100%"><img src="images/filler.gif" width="1" height="1"></TD></TR>
	        <TR>
	        	<TD>Onderbreken Stemming. Na deze actie is het niet meer mogelijk te stemmen totdat de stemming hervat wordt.</TD>
	        </TR>					        	
	        <TR>					        	
	        	<TD align="right"><input type="submit" name="submit" value="Onderbreken Stemming" alt="druk op verder om de verkiezing te onderbreken"></TD>
	        </TR>
			<TR bgcolor="#CCCCCC"><TD width="100%"><img src="images/filler.gif" width="1" height="1"></TD></TR>					        
	</TABLE>

	</FORM>
			
	<%
			} else if (sAvailableState.equals(SystemState.READY_TO_COUNT)) {
	%>
	<FORM name="prepare_vote_count_form" action="ChangeStatePrepareVoteCount" method="POST" enctype="multipart/form-data" onsubmit="return setPinCodes(document.prepare_vote_count_form)">
	<input type="hidden" name="pincode1">
	<input type="hidden" name="pincode2">					
	<TABLE border="0" width="100%">
	        <TR><TD colspan="2"><b>Bereid het systeem voor om de stemopneming uit te voeren</b></TD></TR>        					
			<TR bgcolor="#CCCCCC"><TD colspan="2" width="100%"><img src="images/filler.gif" width="1" height="1"></TD></TR>
			<TR><TD colspan="2">Voer uw wachtwoord en de lokatie van het bestand met uw private key in om de voorbereiding voor de stemopneming te starten.</TD><TD></TD></TR>
	        <TR><TD><BR></TD><TD><BR></TD></TR>        
	        <TR><TD>Private Key file</TD><TD><INPUT type="file" name="<%= PrepareVoteCountCommand.PRIVATE_KEY_NAME %>"></TD></TR>
	        <TR><TD>Wachtwoord</TD><TD><input type="password" name="<%= PrepareVoteCountCommand.PASSWORD_NAME %>"></TD></TR>        
	        <TR><TD><BR></TD><TD><BR></TD></TR>        
	        <TR><TD></TD><TD align="right"><input name="submit" value="Voorbereiden stemopneming" type="submit" alt="druk op verder om het voorbereiden van de stemopneming te starten"></TD></TR>
			<TR bgcolor="#CCCCCC"><TD colspan="2" width="100%"><img src="images/filler.gif" width="1" height="1"></TD></TR>
	</TABLE>
	</FORM>			
	<%
			} else if (sAvailableState.equals(SystemState.VOTES_COUNTED)) {
	%>
    <FORM name="count_vote_form" action="ChangeStateCountVote" method="POST" onsubmit="return setPinCodes(document.count_vote_form)">
    <input type="hidden" name="pincode1">
    <input type="hidden" name="pincode2">					
    <TABLE border="0" width="100%">
      <TR><TD><b>Tel de stemmen</b></TD></TR>        					
      <TR bgcolor="#CCCCCC"><TD width="100%"><img src="images/filler.gif" width="1" height="1"></TD></TR>
      <TR>
        <TD>Tel de stemmen. De stemopneming wordt uitgevoerd en de verkiezingsuitslag wordt bepaald. Op de rapporten pagina kunt u het rapport met de verkiezingsuitslag opvragen.</TD>
      </TR>					        	
      <TR>					        	
	    <TD align="right"><input type="submit" name="submit" value="Stemopneming" alt="druk op verder om de stemopneming te starten"></TD>
	  </TR>
	  <TR bgcolor="#CCCCCC"><TD width="100%"><img src="images/filler.gif" width="1" height="1"></TD></TR>					        
	</TABLE>

    </FORM>		
	<%
	    }
	  }
	%>
	<table>
	  <tr>
	    <td colspan="3" align="left">
	      <BUTTON STYLE="width:200" ONCLICK="window.location='Index'">Terug naar statusoverzicht</BUTTON>
	    </td>
	  </tr>
	</table>
    </td>
    <td width="3%" align="right" height="380"><img src="images/blueline_3.gif" width="1" height="550"></td>
  </tr>
  <tr valign="top">
    <td colspan="3" height="10"><img src="images/horizontalline_2.gif" width="726" height="1"></td>
  </tr>
  <tr valign="top">
    <td colspan="3">
      <div align="center">
      <H2>De verantwoordelijkheid voor deze site berust bij het ministerie van Binnenlandse Zaken en Koninkrijksrelaties</H2>
      </div>
    </td>
  </tr>
</table>
<%@ include file="refreshFooter.jsp" %>		
</BODY>
<HEAD>
<META http-equiv="Pragma" content="no-cache" />
<META http-equiv="Expires" content="-1" />
</HEAD>
</HTML>