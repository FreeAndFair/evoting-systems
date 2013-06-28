<?xml version="1.0" encoding="utf-8" ?> 
<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">

<xsl:template match="REPORT">
<HTML>
	<HEAD>
		<TITLE>Kiezen op afstand - Databeheer - Rapporten - Dagstanden tellers</TITLE>
		<LINK href="VoorzitterWeb.css" rel="stylesheet" type="text/css" />
	</HEAD>
	<BODY>
		
		<TABLE border="0" cellpadding="0" cellspacing="0" width="100%">
			<TR><TD align="center">
				<H1>Dagstanden tellers</H1>	
			</TD></TR>			
			<TR><TD>
			<xsl:apply-templates select="GLOBAAL"/>	
			<xsl:apply-templates select="COUNTERS"/>				
			</TD></TR>
		</TABLE> 
	</BODY>
</HTML>
</xsl:template>

<xsl:template name="globaal" match="REPORT/GLOBAAL">
	<TABLE border="0" cellpadding ="0" cellspacing="0" width="100%">
		<TR bgcolor="#CCCCCC">
			<TD>Stembureau</TD>
			<TD></TD>
			<TD><xsl:value-of select="@STEMBUREAU"/></TD>	
		</TR>
		<TR bgcolor="#CCCCCC">
			<TD>Omschrijving verkiezing</TD>
			<TD></TD>
			<TD><xsl:value-of select="@VERKIEZING"/></TD>	
		</TR>
		<TR bgcolor="#CCCCCC">
			<TD>Start periode</TD>
			<TD></TD>
			<TD><xsl:value-of select="@PERIODE_START"/></TD>	
		</TR>
		<TR bgcolor="#CCCCCC">
			<TD>Eind periode</TD>
			<TD></TD>
			<TD><xsl:value-of select="@PERIODE_EIND"/></TD>	
		</TR>
		<TR bgcolor="#CCCCCC">
			<TD>Huidige status</TD>
			<TD></TD>
			<TD><xsl:value-of select="@STATE"/></TD>	
		</TR>
	</TABLE>
	<xsl:apply-templates select="KIESKRINGEN"/>	
</xsl:template>

<xsl:template name="kieskringen" match="REPORT/GLOBAAL/KIESKRINGEN">
	<H1>Kieskringen</H1>

	<TABLE border="0" cellpadding ="0" cellspacing="0" width="100%">
		<TR bgcolor="#CCCCCC">
			<TD>Naam</TD>
			<TD></TD>
			<TD>Nummer</TD>	
		</TR>
		<xsl:apply-templates select="KIESKRING"/>	
	</TABLE>

</xsl:template>

<xsl:template name="kieskring" match="REPORT/GLOBAAL/KIESKRINGEN/KIESKRING">
		<TR>
			<TD><xsl:value-of select="@NAAM"/></TD>
			<TD></TD>
			<TD><xsl:value-of select="@NUMMER"/></TD>	
		</TR>
</xsl:template>

<xsl:template name="counters" match="REPORT/COUNTERS">
	<H1>Tellerstanden</H1>
	<xsl:apply-templates select="COUNTERGROUP"/>	
</xsl:template>

<xsl:template name="countergroup" match="REPORT/COUNTERS/COUNTERGROUP">

	<TABLE border="0" cellpadding ="0" cellspacing="0" width="100%">
		<TR>
			<TD>Tellersstanden van: <xsl:value-of select="@TIMESTAMP"/></TD>
			<TD>opgeslagen vanuit actie: <xsl:value-of select="@ACTION"/></TD>
		</TR>
	</TABLE>
	
	<TABLE border="0" cellpadding ="0" cellspacing="0" width="100%">
		<TR bgcolor="#CCCCCC">
			<TD>Component</TD>
			<TD></TD>
			<TD>Teller</TD>	
			<TD></TD>
			<TD>Waarde</TD>	
		</TR>
		<xsl:apply-templates select="COUNTER"/>	
	</TABLE>
	<br/>
</xsl:template>

<xsl:template name="counter" match="REPORT/COUNTERS/COUNTERGROUP/COUNTER">
		<TR>
			<TD><xsl:value-of select="@COMPONENT_TYPE"/></TD>
			<TD></TD>
			<TD><xsl:value-of select="@COUNTER_ID"/></TD>	
			<TD></TD>
			<TD><xsl:value-of select="@COUNTER_VALUE"/></TD>	
		</TR>
</xsl:template>

<xsl:template match="GLOBAAL"></xsl:template>
<xsl:template match="KIESKRINGEN"></xsl:template>
<xsl:template match="KIESKRING"></xsl:template>
<xsl:template match="STATISTICS"></xsl:template>
<xsl:template match="ROW"></xsl:template>
<xsl:template match="COUNTERS"></xsl:template>
<xsl:template match="COUNTERGROUP"></xsl:template>
<xsl:template match="COUNTER"></xsl:template>

</xsl:stylesheet>