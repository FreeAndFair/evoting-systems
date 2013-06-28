<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN">
<HTML>
<HEAD>
<META name="GENERATOR" content="IBM WebSphere Studio">
<META http-equiv="Pragma" content="no-cache"/>
<META http-equiv="Expires" content="-1"/>
<TITLE>Kiezen op afstand - Databeheer functionaliteit</TITLE>
<LINK href="DatabeheerWeb.css" rel="stylesheet" type="text/css">
</HEAD>
<%
	com.logicacmg.koa.databeheer.command.SelectUploadCommand command = 
				(com.logicacmg.koa.databeheer.command.SelectUploadCommand) request.getAttribute("COMMAND");
				
	String sMessage = command.getMessage();
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
							<strong>Verkiezing voor de leden van het Europees Parlement 2004</strong></font>
						</div>
					</td>
				</tr>
				</table>
			</div></td>  
            </tr>
            <tr valign="top">
                <td width="3%" align="left" height="380"><img src="images/blueline_3.gif" width="1" height="380"></td>
                <td width="94%" valign="top" height="360">
                	<FORM action="UploadKieslijst" method="POST" enctype="multipart/form-data">
	                <table width="100%" height="100%" border="0" cellpadding="0" cellspacing="0">
                      <tr>
   		                <TD colspan="2">
   		                  Locatie kandidatenlijst:<INPUT type="file" name="upload">
   		                </TD>
     	              </tr>
 		              <tr>
   		                <TD colspan="2"><h3><%= sMessage %></h3></TD>
     	              </tr>
      	              <TR>
				        <td ALIGN="left">
				          <BUTTON STYLE="width:200" ONCLICK="window.location='index.jsp'">Terug naar hoofdpagina</BUTTON>
				        </td>
				        <td>
                          <input ALIGN="right" type="submit" name="verwerk_lijst" value="Verwerk lijst" width="108" height="46" border="0" alt="druk op verder om de kandidatenlijst aan te bieden">
                        </td>
         	          </TR>
          	        </table>
                    </FORM>
                </td>
                <td width="3%" align="right" height="380"><img src="images/blueline_3.gif" width="1" height="380"></td>
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
</BODY>
<HEAD>
<META http-equiv="Pragma" content="no-cache"/>
<META http-equiv="Expires" content="-1"/>
</HEAD>
</HTML>
