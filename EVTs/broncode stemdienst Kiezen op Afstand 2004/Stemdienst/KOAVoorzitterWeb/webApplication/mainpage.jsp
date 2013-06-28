<%@page import="com.logicacmg.koa.voorzitter.command.*"%>
<%@page import="com.logicacmg.koa.constants.*"%>
<%@page import="com.logicacmg.koa.reportserver.KOAStatusReportData"%>
<%@page import="java.util.Calendar"%>
<%@page import="java.util.GregorianCalendar"%>

<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN">
<HTML>
<%
   com.logicacmg.koa.voorzitter.command.IndexPaginaCommand xCommand = (IndexPaginaCommand) request.getAttribute(CommandConstants.COMMAND_IN_REQUEST_KEY);

   String sDutchCurrentState = "Niet bekend";
   if (xCommand != null)
   {
      sDutchCurrentState = SystemState.getDutchTranslationForState(xCommand.getCurrentState());	
   }
   
   KOAStatusReportData koa_status_report_data   = new KOAStatusReportData();
   int				   totaal_kiezers		    = koa_status_report_data.getTotaalKiezers();
   int				   uitgesloten_kiezers	    = koa_status_report_data.getUitgeslotenKiezers();
   int				   kies_gerechtigd		    = totaal_kiezers - uitgesloten_kiezers;
   int				   al_gestemd_web		    = koa_status_report_data.getAlGestemdWeb();
   int				   al_gestemd_tel		    = koa_status_report_data.getAlGestemdTel();
   int				   kiezers_reeds_gestemd    = al_gestemd_web + al_gestemd_tel;
   int                 kiezers_nog_niet_gestemd = kies_gerechtigd - kiezers_reeds_gestemd;
   int				   geblokkeerde_kiezers	    = koa_status_report_data.getGeblokkeerdeKiezers();
   int				   esb_stemmen				= koa_status_report_data.getESBStemmen();
   
   Calendar calendar    = new GregorianCalendar();
   // Year
   int      year        = calendar.get(Calendar.YEAR);
   String   yearString  = "" + year;
   // Month
   int      month       = calendar.get(Calendar.MONTH) + 1;
   String   monthString = "" + month;
   if( month < 10 )
   {
     monthString = "0" + monthString;
   }
   // Day
   int      day     = calendar.get(Calendar.DAY_OF_MONTH);
   String dayString = "" + day;
   if( day < 10 )
   {
      dayString = "0" + dayString;
   }
   // Hour
   int    hour       = calendar.get(Calendar.HOUR_OF_DAY);
   String hourString = "" + hour;
   if( hour < 10 )
   {
      hourString = "0" + hourString;
   }
   // Minute
   int    minute       = calendar.get(Calendar.MINUTE);
   String minuteString = "" + minute;
   if( minute < 10 )
   {
      minuteString = "0" + minuteString;
   }
   // Second
   int    second       = calendar.get(Calendar.SECOND);
   String secondString = "" + second;
   if( second < 10 )
   {
      secondString = "0" + secondString;
   }
%>
<HEAD>
<META http-equiv="Pragma" content="no-cache"/>
<META http-equiv="Expires" content="-1"/>
<META http-equiv="Refresh" content="60;URL=Index" />
<META name="GENERATOR" content="IBM WebSphere Studio">
<TITLE>Kiezen op afstand - Voorzitter - Hoofdmenu</TITLE>
<LINK href="VoorzitterWeb.css" rel="stylesheet" type="text/css">
</HEAD>
<BODY>

<!---------------------------------------------------
  -- TABLE TO DIVIDE SCREEN IN TWO ROWS:
  -- 1) TOP ROW WITH BANNER
  -- 2) CENTER ROW WITH MENU LEFT AND STATUSREPORT RIGHT
  -------------------------------------------------->
<TABLE WIDTH="100%" HEIGHT="100%" BORDER="0" CELLSPACING="0" CELLPADDING="0">
  <TR>
    <TD COLSPAN="2" BACKGROUND="images/banner_filler.gif" >
      <TABLE>
        <TR>
    	  <td colspan="3"><div align="left">
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
          <TD ALIGN="right">
            <FONT COLOR="white">
            <CENTER>
            <%= dayString %>/<%= monthString %>/<%= yearString %><BR><BR>
            <%= hourString%>:<%= minuteString %>:<%= secondString %>
            </CENTER>
            </FONT>
          </TD>
        </TR>
      </TABLE>
    </TD>
  </TR>
  <TR>
    <TD WIDTH="10%">
        <!----------------------------------------------------
          -- TABLE TO SHOW THE MENU ON THE LEFT OF THE SCREEN
          ---------------------------------------------------->
        <TABLE WIDTH="100%" HEIGHT="100%" BORDER="1" BORDERCOLOR="white">
          <TR>
            <TD VALIGN="top" BORDERCOLOR="blue">
              <% 
                 if(xCommand == null || !xCommand.getCurrentState().equals(SystemState.VOTES_COUNTED))
                 {
              %>
                  <BUTTON STYLE="width:100" ONCLICK="window.location='GetCurrentState'">Wijzig<BR>status</BUTTON><BR><BR>
              <% }
                 else {
              %>
                  <BUTTON STYLE="width:100" DISABLED>Wijzig<BR>status</BUTTON><BR><BR>
              <% } %>
              <BUTTON STYLE="width:100" ONCLICK="window.location='ShowReports'">Rapporten</BUTTON><BR><BR>
              <BUTTON STYLE="width:100" ONCLICK="window.location='FetchData'">Ophalen<BR>gegevens</BUTTON><BR><BR>
              <% 
                 if(xCommand == null || !xCommand.getCurrentState().equals(SystemState.OPEN))
                 {
              %>
                  <BUTTON STYLE="width:100" ONCLICK="window.location='CompareFingerprints'">Vinger<BR>afdruk</BUTTON>
              <% }
                 else {
              %>
                  <BUTTON STYLE="width:100" DISABLED>Vinger<BR>afdruk</BUTTON>
              <% } %>
            </TD>
          </TR>
        </TABLE>
    </TD>
    <TD WIDTH="90%">
      <!----------------------------------------------------
        -- TABLE TO SHOW TWO ROWS:
        -- 1) THE STATUSREPORT ON THE TOP
        -- 2) SOME OTHER INFO ON THE BOTTOM
        --------------------------------------------------->
      <TABLE WIDTH="100%" HEIGHT="100%" BORDER="1" BORDERCOLOR="white">
        <TR HEIGHT="80%">
          <TD BORDERCOLOR="blue">
            <TABLE WIDTH="100%" HEIGHT="100%">
              <TR>
                <TD ALIGN="left" WIDTH="33%">
                  <TABLE WIDTH="100%" HEIGHT="100%">
                    <TR HEIGHT="50%">
                      <TD VALIGN="bottom">
                        <TABLE WIDTH="100%" HEIGHT="100%" CELLSPACING="0" CELLPADDING="5" BORDER="1" BORDERCOLOR="black" frame="box" rules="none">
                          <TR HEIGHT="40">
                            <TH ALIGN="left" COLSPAN="2" nowrap>Kiesregister</TH>
                          </TR>
                          <TR HEIGHT="40">
                            <TD ALIGN="right" nowrap>Aantal personen:</TD>
                            <TD ALIGN="right" nowrap><%= totaal_kiezers %></TD>
                          </TR>
                          <TR HEIGHT="40">
                            <TD ALIGN="right" nowrap>Waarvan uitgesloten:</TD>
                            <TD ALIGN="right" nowrap><U><%= uitgesloten_kiezers %></U></TD>
                          </TR>
                          <TR HEIGHT="40">
                            <TD ALIGN="right" nowrap>Waarvan kiesgerechtigd:</TD>
                            <TD ALIGN="right" nowrap><%= kies_gerechtigd %></TD>
                          </TR>
                        </TABLE>
                      </TD>
                      <TD VALIGN="bottom">
                        <img src="images/horizontal_arrow.gif" width="48" height="30">
                      </TD>
                    </TR>
                    <TR COLSPAN="2" HEIGHT="50%">
                      <TD></TD>
                    </TR>
                  </TABLE>
                </TD>
                <TD WIDTH="33%">
                  <TABLE WIDTH="100%" HEIGHT="100%">
                    <TR HEIGHT="20%">
                      <TD></TD>
                    </TR>
                    <TR HEIGHT=40%">
                      <TD ALIGN="right" VALIGN="bottom">
                        <TABLE WIDTH="100%" HEIGHT="100%" CELLSPACING="0" CELLPADDING="5" BORDER="1" BORDERCOLOR="black" frame="box" rules="none">
                          <TR HEIGHT="40">
                            <TH ALIGN="left" COLSPAN="2" nowrap>Stemming</TH>
                          </TR>
                          <TR HEIGHT="40">
                            <TD ALIGN="right" nowrap>Nog niet gestemd:</TD>
                            <TD ALIGN="right" nowrap><%= kiezers_nog_niet_gestemd %></TD>
                          </TR>
                          <TR HEIGHT="40">
                            <TD ALIGN="right" nowrap>Reeds gestemd:</TD>
                            <TD ALIGN="right" nowrap><FONT COLOR="red"><%= kiezers_reeds_gestemd %></FONT></TD>
                          </TR>
                        </TABLE>
                      </TD>
                    </TR>
                    <TR HEIGHT="20%">
                      <TD ALIGN="right">
                        <img src="images/vertical_arrow.gif" width="21" height="64">
                      </TD>
                    </TR>
                    <TR HEIGHT="20%">
                      <TD ALIGN="right">
                        <TABLE WIDTH="100%" HEIGHT="100%" CELLSPACING="0" CELLPADDING="5" BORDER="1" BORDERCOLOR="black" frame="box" rules="none">
                          <TR>
                            <TH ALIGN="left" COLSPAN="2" nowrap>Stembus</TH>
                          </TR>
                          <TR HEIGHT="40">
                            <TD ALIGN="right" nowrap>Reeds gestemd:</TD>
                            <TD ALIGN="right" nowrap><FONT COLOR="red"><%= esb_stemmen %></FONT></TD>
                          </TR>
                        </TABLE>
                      </TD>
                    </TR>
                  </TABLE>
                <TD WIDTH="33%">
                  <TABLE WIDTH="100%" HEIGHT="100%">
                    <TR HEIGHT="50%">
                      <TD></TD>
                    </TR>
                    <TR HEIGHT=30%">
                      <TD ALIGN="left" VALIGN="top">
                        <img src="images/horizontal_arrow.gif" width="48" height="30">
                      </TD>
                      <TD ALIGN="center" VALIGN="top">
                        <TABLE WIDTH="100%" HEIGHT="100%" CELLSPACING="0" CELLPADDING="5" BORDER="1" BORDERCOLOR="black" frame="box" rules="none">
                          <TR HEIGHT="40">
                            <TH ALIGN="left" COLSPAN="2" nowrap>Manier van stemmen</TH>
                          </TR>
                          <TR HEIGHT="40">
                            <TD ALIGN="right" nowrap>Via Internet:</TD>
                            <TD ALIGN="right" nowrap><%= al_gestemd_web %></TD>
                          </TR>
                          <TR HEIGHT="40">
                            <TD ALIGN="right" nowrap>Via telefoon:</TD>
                            <TD ALIGN="right" nowrap><%= al_gestemd_tel %></TD>
                          </TR>
                        </TABLE>
                      </TD>
                    </TR>
                    <TR HEIGHT="20%">
                      <TD></TD>
                    </TR>
                  </TABLE>
                </TD>
              </TR>
            </TABLE>
          </TD>
        </TR>
        <TR HEIGHT="20%">
          <TD BORDERCOLOR="blue">
            <TABLE WIDTH="100%" HEIGHT="100%">
              <TR>
                <TD ALIGN="left" WIDTH="34%">
                  <TABLE WIDTH="100%" HEIGHT="100%" CELLSPACING="0" CELLPADDING="5" BORDER="1" BORDERCOLOR="black" FRAMES="box" RULES="none">
                    <TR>
                      <TH ALIGN="left">Status</TH>
                    </TR>
                    <TR>
                      <TD><%= sDutchCurrentState %></TD>
                    </TR>
                  </TABLE>
                </TD>
                <TD ALIGN="right" WIDTH="66%">
                  <TABLE WIDTH="100%" HEIGHT="100%" CELLSPACING="0" CELLPADDING="5" BORDER="1" BORDERCOLOR="black" FRAMES="box" RULES="none">
                    <TR>
                      <TH ALIGN="left" COLSPAN="2">Indicaties misbruik</TH>
                    </TR>
                    <TR>
                      <TD ALIGN="left">Aantal tijdelijk geblokkeerde stemcodes:</TD>
                      <TD ALIGN="right"><%= geblokkeerde_kiezers %></TD>
                    </TR>
                  </TABLE>
                </TD>
              </TR>
            </TABLE>
          </TD>
        </TR>
      </TABLE>
    </TD>
  </TR>
</TABLE>

</BODY>
</HTML>