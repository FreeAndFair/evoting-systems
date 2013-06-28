<?xml version="1.0"?>

<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform" xmlns:fo="http://www.w3.org/1999/XSL/Format" exclude-result-prefixes="fo">
<xsl:output method="xml" version="1.0" omit-xml-declaration="no" indent="yes"/>

<!-- FO root -->
<xsl:template match="/report">
	<fo:root xmlns:fo="http://www.w3.org/1999/XSL/Format">
		<fo:layout-master-set>
			<fo:simple-page-master master-name="simpleA4" page-height="29.7cm" page-width="21cm" margin-top="2cm" margin-bottom="2cm" margin-left="2cm" margin-right="2cm">
			<fo:region-body/>
			</fo:simple-page-master>
		</fo:layout-master-set>
		<fo:page-sequence master-reference="simpleA4">
			<fo:flow flow-name="xsl-region-body">
			<fo:block space-after.optimum="10pt" font-size="16pt">
			<!-- Roep de juiste templates aan ahv het soort bestand -->
			Verwerkingsverslag <xsl:value-of select="/report/data/import/contenttype"/>
			</fo:block>

			<xsl:call-template name="verslag"/>

			</fo:flow>
		</fo:page-sequence>
	</fo:root>
</xsl:template>

<!-- END OF ROOT -->
<!-- Specific templates -->

<xsl:template name="verslag" match="/report/data">
<fo:block space-after.optimum="10pt">
	<xsl:apply-templates select="/report/data/import"/>
</fo:block>
<fo:block space-after.optimum="10pt">
	<xsl:apply-templates select="/report/data/time"/>	
</fo:block>
<fo:block space-after.optimum="10pt">
	<xsl:apply-templates select="/report/data/metadata"/>
</fo:block>
<fo:block space-after.optimum="10pt">
Aantal aangetroffen in bestand:
<!--	<xsl:apply-templates select="/report/data/numberofrecords"/> -->
</fo:block>

<fo:block space-after.optimum="10pt">
<fo:table border="0pt solid black" text-align="left">
	<fo:table-column column-width="80mm"/>
	<fo:table-column column-width="80mm"/>
	<fo:table-body>
		<xsl:apply-templates select="/report/data/count"/>
	</fo:table-body>
</fo:table>
</fo:block>

<fo:block space-after.optimum="10pt">
Aantal niet gevonden referenties:
</fo:block>

<fo:block space-after.optimum="10pt">
<fo:table border="0pt solid black" text-align="left">
	<fo:table-column column-width="80mm"/>
	<fo:table-column column-width="80mm"/>
	<fo:table-body>
		<xsl:apply-templates select="/report/data/notfound"/>	
	</fo:table-body>
</fo:table>
</fo:block>

<fo:block space-after.optimum="10pt">
Aantal verwerkt:
</fo:block>

<fo:block space-after.optimum="10pt">
<fo:table border="0pt solid black" text-align="left">
	<fo:table-column column-width="80mm"/>
	<fo:table-column column-width="80mm"/>
	<fo:table-body>
		<xsl:apply-templates select="/report/data/insert"/>	
	</fo:table-body>
</fo:table>
</fo:block>

<fo:block space-after.optimum="10pt">
Aantal niet verwerkt:
</fo:block>

<fo:table border="0pt solid black" text-align="left">
	<fo:table-column column-width="80mm"/>
	<fo:table-column column-width="80mm"/>
	<fo:table-body>
		<xsl:apply-templates select="/report/data/notinsert"/>	
	</fo:table-body>
</fo:table>

</xsl:template>

<xsl:template name="KIESLIJST" match="/report/data">
Verwerkingsverslag kieslijst:
	<xsl:apply-templates/>
</xsl:template>

<xsl:template match="/report/data/metadata">
<fo:block space-after.optimum="10pt">
<fo:table border="0pt solid black" text-align="left">
	<fo:table-column column-width="80mm"/>
	<fo:table-column column-width="80mm"/>
	<fo:table-body>
		<fo:table-row>
			<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
				<fo:block>Tijdstempel verwerkingsbestand:</fo:block>
			</fo:table-cell>
			<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
				<fo:block>
				<xsl:value-of select="substring(creationtime,6,2)"/>.<xsl:value-of select="substring(creationtime,9,2)"/>.<xsl:value-of select="substring(creationtime,1,4)"/>
				&#xa0;<xsl:value-of select="substring(creationtime,12,8)"/>
				</fo:block>
			</fo:table-cell>
		</fo:table-row>
		<fo:table-row>
			<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
				<fo:block>Referentienummer verwerkingsbestand:</fo:block>
			</fo:table-cell>
			<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
				<fo:block><xsl:value-of select="requestreference"/></fo:block>
			</fo:table-cell>
		</fo:table-row>
<!--
		<fo:table-row>
			<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
				<fo:block>Aantal records in retourbestand:</fo:block>
			</fo:table-cell>
			<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
				<fo:block><xsl:value-of select="/report/data/numberofrecords"/></fo:block>
			</fo:table-cell>
		</fo:table-row>
-->
	</fo:table-body>
</fo:table>
</fo:block>
<!-- counters a.h.v. type bestand -->
<fo:block space-after.optimum="10pt">
Aantal volgens de bestandsheader:
</fo:block>

<fo:table border="0pt solid black" text-align="left">
	<fo:table-column column-width="80mm"/>
	<fo:table-column column-width="80mm"/>
	<fo:table-body>
		<xsl:apply-templates/>
	</fo:table-body>
</fo:table>			
</xsl:template>

<xsl:template match="/report/data/metadata/*">
	<xsl:if test="name() != 'creationtime' and name() != 'requestreference'">
		<fo:table-row>
			<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
				<fo:block><xsl:value-of select="substring-before(name(),'count')"/>:</fo:block>
			</fo:table-cell>
			<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
				<fo:block><xsl:value-of select="."/></fo:block>
			</fo:table-cell>
		</fo:table-row>
	</xsl:if>
</xsl:template>

<xsl:template match="/report/data/time">
<fo:table border="0pt solid black" text-align="left">
	<fo:table-column column-width="80mm"/>
	<fo:table-column column-width="80mm"/>
	<fo:table-body>
		<fo:table-row>
			<fo:table-cell padding="2pt" border="0pt solid black" background-color="white">
				<fo:block>Tijdstip start verwerking: </fo:block>
			</fo:table-cell>
			<fo:table-cell padding="2pt" border="0pt solid black" background-color="white">
				<fo:block><xsl:value-of select="start"/></fo:block>
			</fo:table-cell>
		</fo:table-row>
		<fo:table-row>
			<fo:table-cell padding="2pt" border="0pt solid black" background-color="white">
				<fo:block>Tijdstip einde verwerking: </fo:block>
			</fo:table-cell>
			<fo:table-cell padding="2pt" border="0pt solid black" background-color="white">
				<fo:block><xsl:value-of select="end"/></fo:block>
			</fo:table-cell>
		</fo:table-row>
	</fo:table-body>
</fo:table>


</xsl:template>

<xsl:template match="/report/data/import">
<fo:table border="0pt solid black" text-align="left">
	<fo:table-column column-width="80mm"/>
	<fo:table-column column-width="80mm"/>
	<fo:table-body>
		<fo:table-row>
			<fo:table-cell padding="2pt" border="0pt solid black" background-color="white">
				<fo:block>Type verwerking:</fo:block>
			</fo:table-cell>
			<fo:table-cell padding="2pt" border="0pt solid black" background-color="white">
				<fo:block><xsl:value-of select="action"/></fo:block>
			</fo:table-cell>
		</fo:table-row>
	</fo:table-body>
</fo:table>

</xsl:template>

<xsl:template match="/report/data/count/*">
	<xsl:call-template name="row"/>
</xsl:template>

<xsl:template match="/report/data/notfound/*">
	<xsl:call-template name="row"/>
</xsl:template>

<xsl:template match="/report/data/insert/*">
	<xsl:call-template name="row"/>
</xsl:template>

<xsl:template match="/report/data/notinsert/*">
	<xsl:call-template name="row"/>
</xsl:template>

<xsl:template match="/report/data/numberofrecords"/>
<xsl:template name="row">
	<fo:table-row>
		<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
			<fo:block><xsl:value-of select="name()"/>:</fo:block>
		</fo:table-cell>
		<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
			<fo:block><xsl:value-of select="."/></fo:block>
		</fo:table-cell>
	</fo:table-row>
</xsl:template>

</xsl:stylesheet>
