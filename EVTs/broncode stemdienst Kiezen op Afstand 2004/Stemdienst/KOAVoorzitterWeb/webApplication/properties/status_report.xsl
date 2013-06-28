<?xml version="1.0" encoding="UTF-8" ?> 
<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">

<xsl:template match="REPORT">
<HTML>
<HEAD>
<META http-equiv="Content-Type" content="text/html; charset=UTF-8"/>
<TITLE>Kiezen op afstand - Voorzitter - Rapporten - Statusrapport</TITLE>
<LINK type="text/css" rel="stylesheet" href="VoorzitterWeb_statusreport.css"/>
</HEAD>
<BODY>

<h1 align="center">Statusrapport</h1>

<xsl:apply-templates select="GLOBAAL"/>

<TABLE BORDER="1" WIDTH="100%" CELLSPACING="0" CELLPADDING="0">
  <TR>
    <TD WIDTH="61%"> </TD>
    <TD WIDTH="13%" ALIGN="center"><b>Per internet</b></TD>
    <TD WIDTH="13%" ALIGN="center"><b>Per telefoon</b></TD>
    <TD WIDTH="13%" ALIGN="center"><b>Totaal</b></TD>
  </TR>
  <TR>
    <TD WIDTH="61%">Aantal kiesgerechtigden dat zijn stem heeft uitgebracht:</TD>
    <TD WIDTH="13%" ALIGN="center"><xsl:apply-templates select="ALREADY_VOTED_WEB"/>&#160;</TD>
	<TD WIDTH="13%" ALIGN="center"><xsl:apply-templates select="ALREADY_VOTED_TEL"/>&#160;</TD>
    <TD WIDTH="13%" ALIGN="center"><xsl:apply-templates select="ESB_STEMMEN_UITGEBRACHT"/>&#160;</TD>
  </TR>
  <TR>
    <TD WIDTH="61%">Aantal kiesgerechtigden dat nog een stem mag uitbrengen:</TD>
    <TD WIDTH="13%" ALIGN="center">.</TD>
    <TD WIDTH="13%" ALIGN="center">.</TD>
    <TD WIDTH="13%" ALIGN="center"><xsl:apply-templates select="NOT_VOTED_YET"/>&#160;</TD>
  </TR>
</TABLE>

<H2>Detailgegevens</H2>
<H3>Kiezersregistratie</H3>
<TABLE BORDER="1" WIDTH="100%" CELLSPACING="0" CELLPADDING="0">
  <TR>
    <TD WIDTH="74%" VALIGN="top"> </TD>
    <TD WIDTH="26%" VALIGN="top" ALIGN="center"><b>Totaal</b></TD>
  </TR>
  <TR>
    <TD WIDTH="74%" VALIGN="top">Totaal aantal kiesgerechtigden in de 
      kiezersregistratie:</TD>
    <TD WIDTH="26%" VALIGN="top" ALIGN="center">
      <xsl:apply-templates select="STEMMERS"/>&#160;
    </TD>
  </TR>
</TABLE>


<H3>Inlogpogingen</H3>
<TABLE BORDER="1" WIDTH="100%" HEIGHT="90" CELLSPACING="0" CELLPADDING="0">
  <TR>
    <TD WIDTH="61%" HEIGHT="16" VALIGN="top"> </TD>
    <TD WIDTH="13%" HEIGHT="16" VALIGN="top" ALIGN="center"><b>Per internet</b></TD>
    <TD WIDTH="13%" HEIGHT="16" VALIGN="top" ALIGN="center"><b>Per telefoon</b></TD>
    <TD WIDTH="13%" HEIGHT="16" VALIGN="top" ALIGN="center"><b>Totaal</b></TD>
  </TR>
  <TR>
    <TD WIDTH="61%" HEIGHT="48" VALIGN="top">Aantal kiezers dat verbinding heeft 
      gezocht (verbinding zoeken betekent in geval van internet: proberen in te 
      loggen. In geval van telefoon: bellen) in de periode dat de stemming open 
      is (geweest):</TD>
    <TD WIDTH="13%" HEIGHT="48" VALIGN="top" ALIGN="center"><xsl:apply-templates select="WEB_OPROEPEN_BEDRIJF"/>&#160;</TD>
    <TD WIDTH="13%" HEIGHT="48" VALIGN="top" ALIGN="center"><xsl:apply-templates select="TEL_OPROEPEN_BEDRIJF"/>&#160;</TD>
    <TD WIDTH="13%" HEIGHT="48" VALIGN="top" ALIGN="center"><xsl:apply-templates select="WEB_TEL_OPROEPEN_BEDRIJF"/>&#160;</TD>
  </TR>
  <TR>
    <TD WIDTH="61%" HEIGHT="8" VALIGN="top">Aantal kiezers dat verbinding heeft 
      gezocht (verbinding zoeken betekent in geval van internet: proberen in te 
      loggen. In geval van telefoon: bellen) in de periode dat de stemming niet 
      in bedrijf was (vóór opening, tijdens een eventuele onderbreking en na 
      sluiting):</TD>
    <TD WIDTH="13%" HEIGHT="8" VALIGN="top" ALIGN="center"><xsl:apply-templates select="WEB_OPROEPEN_BUITEN_BEDRIJF"/>&#160;</TD>
    <TD WIDTH="13%" HEIGHT="8" VALIGN="top" ALIGN="center"><xsl:apply-templates select="TEL_OPROEPEN_BUITEN_BEDRIJF"/>&#160;</TD>
    <TD WIDTH="13%" HEIGHT="8" VALIGN="top" ALIGN="center"><xsl:apply-templates select="WEB_TEL_OPROEPEN_BUITEN_BEDRIJF"/>&#160;</TD>
  </TR>
  <TR>
    <TD WIDTH="61%" HEIGHT="8" VALIGN="top">Aantal kiezers dat heeft ingelogd:</TD>
    <TD WIDTH="13%" HEIGHT="8" VALIGN="top" ALIGN="center"><xsl:apply-templates select="WEB_VERIFICATIE_GELUKT"/>&#160;</TD>
    <TD WIDTH="13%" HEIGHT="8" VALIGN="top" ALIGN="center"><xsl:apply-templates select="TEL_VERIFICATIE_GELUKT"/>&#160;</TD>
    <TD WIDTH="13%" HEIGHT="8" VALIGN="top" ALIGN="center"><xsl:apply-templates select="WEB_TEL_VERIFICATIE_GELUKT"/>&#160;</TD>
  </TR>
  <TR>
    <TD WIDTH="61%" HEIGHT="8" VALIGN="top">Aantal mislukte pogingen om in te 
      loggen:</TD>
    <TD WIDTH="13%" HEIGHT="8" VALIGN="top" ALIGN="center"><xsl:apply-templates select="WEB_VERIFICATIE_MISLUKT"/>&#160;</TD>
    <TD WIDTH="13%" HEIGHT="8" VALIGN="top" ALIGN="center"><xsl:apply-templates select="TEL_VERIFICATIE_MISLUKT"/>&#160;</TD>
    <TD WIDTH="13%" HEIGHT="8" VALIGN="top" ALIGN="center"><xsl:apply-templates select="WEB_TEL_VERIFICATIE_MISLUKT"/>&#160;</TD>
  </TR>
  <TR>
    <TD WIDTH="61%" HEIGHT="8" VALIGN="top">Aantal kiezers dat op dit 
      moment tijdelijk geblokkeerd is (niet mogen inloggen) wegens herhaaldelijk 
      foutief inloggen:</TD>
    <TD WIDTH="13%" HEIGHT="8" VALIGN="top" ALIGN="center">.</TD>
    <TD WIDTH="13%" HEIGHT="8" VALIGN="top" ALIGN="center">.</TD>
    <TD WIDTH="13%" HEIGHT="8" VALIGN="top" ALIGN="center"><xsl:apply-templates select="BLOCKED"/>&#160;</TD>
  </TR>
</TABLE>

<H3>Aanvullende gegevens telefoonstemmen</H3>
<TABLE BORDER="1" WIDTH="100%" CELLSPACING="0" CELLPADDING="0" HEIGHT="33">
  <TR>
    <TD WIDTH="74%" VALIGN="top" HEIGHT="16"> </TD>
    <TD WIDTH="26%" VALIGN="top" HEIGHT="16" ALIGN="center"><b>Per telefoon</b></TD>
  </TR>
<!--  OR 22.3.284 'in gesprek' not supported
  <TR>
    <TD WIDTH="74%" VALIGN="top" HEIGHT="13">Aantal malen dat kiezers 'in 
      gesprek' hebben gekregen:</TD>
    <TD WIDTH="26%" VALIGN="top" HEIGHT="13" ALIGN="center">      
	    <xsl:apply-templates select="TEL_IN_GESPREK"/>&#160;
	</TD>
  </TR>
-->  
  <TR>
    <TD WIDTH="74%" VALIGN="top" HEIGHT="13">Aantal malen dat het gesprek door 
      kiezers werd afgebroken zonder dat een stem is uitgebracht:</TD>
    <TD WIDTH="26%" VALIGN="top" HEIGHT="13" ALIGN="center">
	    <xsl:apply-templates select="TEL_AFGEBROKEN"/>&#160;
    </TD>
  </TR>
</TABLE>
</BODY>
</HTML>
</xsl:template>

<xsl:template name="globaal" match="REPORT/GLOBAAL">
<DIV ALIGN="right">
  <TABLE BORDER="0" WIDTH="100%">
    <TR>
      <TD WIDTH="50%" ALIGN="right">Datum en tijdstip statusrapport: <B><xsl:value-of select="@CURTIME"/></B></TD>
    </TR>
    <TR>
      <TD WIDTH="50%" ALIGN="right">Naam voorzitter: <xsl:value-of select="@VOORZITTER"/></TD>
    </TR>
  </TABLE>
</DIV>
<H2>Kerngegevens</H2>
<P>
Stemming: <B><xsl:value-of select="@VERKIEZING"/></B>
<BR/>
Status: <xsl:value-of select="@STATE"/>
</P>
</xsl:template>

<xsl:template name="already_voted_web" match="REPORT/ALREADY_VOTED_WEB">
	<xsl:value-of select="@COUNTER_VALUE"/>
</xsl:template>

<xsl:template name="already_voted_tel" match="REPORT/ALREADY_VOTED_TEL">
	<xsl:value-of select="@COUNTER_VALUE"/>
</xsl:template>

<xsl:template name="NOT_VOTED_YET" match="REPORT/NOT_VOTED_YET">
	<xsl:value-of select="@COUNTER_VALUE"/>
</xsl:template>

<xsl:template name="stemmers" match="REPORT/STEMMERS">
	<xsl:value-of select="@COUNTER_VALUE"/>
</xsl:template>

<xsl:template name="TEL_IN_GESPREK" match="REPORT/TEL_IN_GESPREK">
	<xsl:value-of select="@COUNTER_VALUE"/>
</xsl:template>

<xsl:template name="TEL_AFGEBROKEN" match="REPORT/TEL_AFGEBROKEN">
	<xsl:value-of select="@COUNTER_VALUE"/>
</xsl:template>

<xsl:template name="WEB_OPROEPEN_BEDRIJF" match="REPORT/WEB_OPROEPEN_BEDRIJF">
	<xsl:value-of select="@COUNTER_VALUE"/>
</xsl:template>

<xsl:template name="TEL_OPROEPEN_BEDRIJF" match="REPORT/TEL_OPROEPEN_BEDRIJF">
	<xsl:value-of select="@COUNTER_VALUE"/>
</xsl:template>

<xsl:template name="WEB_TEL_OPROEPEN_BEDRIJF" match="REPORT/WEB_TEL_OPROEPEN_BEDRIJF">
	<xsl:value-of select="@COUNTER_VALUE"/>
</xsl:template>

<xsl:template name="WEB_OPROEPEN_BUITEN_BEDRIJF" match="REPORT/WEB_OPROEPEN_BUITEN_BEDRIJF">
	<xsl:value-of select="@COUNTER_VALUE"/>
</xsl:template>

<xsl:template name="TEL_OPROEPEN_BUITEN_BEDRIJF" match="REPORT/TEL_OPROEPEN_BUITEN_BEDRIJF">
	<xsl:value-of select="@COUNTER_VALUE"/>
</xsl:template>

<xsl:template name="WEB_TEL_OPROEPEN_BUITEN_BEDRIJF" match="REPORT/WEB_TEL_OPROEPEN_BUITEN_BEDRIJF">
	<xsl:value-of select="@COUNTER_VALUE"/>
</xsl:template>


<xsl:template name="TEL_VERIFICATIE_GELUKT" match="REPORT/TEL_VERIFICATIE_GELUKT">
	<xsl:value-of select="@COUNTER_VALUE"/>
</xsl:template>

<xsl:template name="WEB_VERIFICATIE_GELUKT" match="REPORT/WEB_VERIFICATIE_GELUKT">
	<xsl:value-of select="@COUNTER_VALUE"/>
</xsl:template>

<xsl:template name="WEB_TEL_VERIFICATIE_GELUKT" match="REPORT/WEB_TEL_VERIFICATIE_GELUKT">
	<xsl:value-of select="@COUNTER_VALUE"/>
</xsl:template>

<xsl:template name="WEB_VERIFICATIE_MISLUKT" match="REPORT/WEB_VERIFICATIE_MISLUKT">
	<xsl:value-of select="@COUNTER_VALUE"/>
</xsl:template>

<xsl:template name="TEL_VERIFICATIE_MISLUKT" match="REPORT/TEL_VERIFICATIE_MISLUKT">
	<xsl:value-of select="@COUNTER_VALUE"/>
</xsl:template>

<xsl:template name="WEB_TEL_VERIFICATIE_MISLUKT" match="REPORT/WEB_TEL_VERIFICATIE_MISLUKT">
	<xsl:value-of select="@COUNTER_VALUE"/>
</xsl:template>

<xsl:template name="WEB_STEMMEN_UITGEBRACHT" match="REPORT/WEB_STEMMEN_UITGEBRACHT">
	<xsl:value-of select="@COUNTER_VALUE"/>
</xsl:template>

<xsl:template name="TEL_STEMMEN_UITGEBRACHT" match="REPORT/TEL_STEMMEN_UITGEBRACHT">
	<xsl:value-of select="@COUNTER_VALUE"/>
</xsl:template>

<xsl:template name="ESB_STEMMEN_UITGEBRACHT" match="REPORT/ESB_STEMMEN_UITGEBRACHT">
	<xsl:value-of select="@COUNTER_VALUE"/>
</xsl:template>

<xsl:template name="GEBLOKKEERD" match="REPORT/BLOCKED">
	<xsl:value-of select="@COUNTER_VALUE"/>
</xsl:template>

</xsl:stylesheet>
