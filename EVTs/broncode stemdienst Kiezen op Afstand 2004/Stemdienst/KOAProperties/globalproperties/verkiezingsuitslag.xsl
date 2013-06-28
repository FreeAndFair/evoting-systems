<?xml version="1.0"?>

<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform" xmlns:fo="http://www.w3.org/1999/XSL/Format" exclude-result-prefixes="fo">
<xsl:output method="xml" encoding="ASCII" version="1.0" omit-xml-declaration="no" indent="yes"/>

<!-- FO root -->
<xsl:template match="/verkiezingsuitslag">
	<fo:root xmlns:fo="http://www.w3.org/1999/XSL/Format">
		<fo:layout-master-set>
			<fo:simple-page-master master-name="simpleA4" page-height="29.7cm" page-width="21cm" margin-top="2cm" margin-bottom="2cm" margin-left="2cm" margin-right="2cm">
			<fo:region-body/>
			</fo:simple-page-master>
		</fo:layout-master-set>
		<fo:page-sequence master-reference="simpleA4">
			<fo:flow flow-name="xsl-region-body">
			<fo:block space-after.optimum="10pt" font-size="16pt"  font-family="Verdana">
			<!-- Roep de juiste templates aan ahv het soort bestand -->
			Resultaat van de stemming
			</fo:block>

			<xsl:apply-templates/>

			</fo:flow>
		</fo:page-sequence>
	</fo:root>
</xsl:template>

<xsl:template match="kieskring">
	<fo:block space-after.optimum="8pt" font-size="14pt" background-color="silver"  font-family="Verdana">
	&#xa0;Kieskring: <xsl:value-of select="@ID"/> - <xsl:value-of select="@Kieskring"/>
	</fo:block>
	<fo:block space-after.optimum="8pt" font-size="14pt" background-color="silver"  font-family="Verdana">
	&#xa0;Stembureau: <xsl:value-of select="@Stembureau"/>
	</fo:block>
	<fo:block space-after.optimum="8pt" font-size="14pt" background-color="silver"  font-family="Verdana">
	&#xa0;Stemperiode: <xsl:value-of select="@StartDatumTijd"/> - <xsl:value-of select="@StopDatumTijd"/>
	</fo:block>
	<fo:block space-after.optimum="8pt" font-size="14pt" background-color="silver"  font-family="Verdana">
	&#xa0;Verkiezing: <xsl:value-of select="@Verkiezing"/>
	</fo:block>
	<fo:block space-after.optimum="8pt" font-size="14pt" background-color="silver"  font-family="Verdana">
	&#xa0;Starttijd stemming: <xsl:value-of select="@StarttijdStemming" />
	</fo:block>
	<fo:block space-after.optimum="8pt" font-size="14pt" background-color="silver"  font-family="Verdana">
	&#xa0;Eindtijd stemming: <xsl:value-of select="@EindtijdStemming" />
	</fo:block>
	<fo:block space-after.optimum="8pt" font-size="14pt" background-color="silver"  font-family="Verdana">
	&#xa0;Aantal kiesgerechtigden: <xsl:value-of select="@KiesGerechtigden"/>
	</fo:block>
	<fo:block space-after.optimum="8pt" font-size="14pt" background-color="silver"  font-family="Verdana">
	&#xa0;Aantal kiesgerechtigden dat heeft gestemd: <xsl:value-of select="@AantalGestemdeKiezers"/>
	</fo:block>	
	<fo:block space-after.optimum="8pt" font-size="14pt" background-color="silver"  font-family="Verdana">
	&#xa0;Aantal kiesgerechtigden dat niet heeft gestemd: <xsl:value-of select="@AantalNietGestemdeKiezers"/>
	</fo:block>	
	
	<xsl:apply-templates/>
</xsl:template>

<xsl:template match="kieslijst">
	<xsl:choose>
	    <xsl:when test="@KiesLijstNummer!=''">
			<fo:block font-size="12pt" background-color="silver" space-after.optimum="8pt"  font-family="Verdana">&#xa0;Lijstnummer: <xsl:value-of select="@KiesLijstNummer"/></fo:block>
			<fo:block font-family="Verdana">Lijstnaam: <xsl:value-of select="@lijstnaam"/></fo:block>
			<fo:block space-after.optimum="10pt" font-family="Verdana">Aantal stemmen: <xsl:value-of select="@totaal_stemmen"/></fo:block>
		</xsl:when>
		<xsl:otherwise>
			<fo:block font-size="12pt" background-color="silver" space-after.optimum="8pt"  font-family="Verdana">&#xa0;<xsl:value-of select="@lijstnaam"/></fo:block>
		</xsl:otherwise>
	</xsl:choose>
	<fo:block space-after.optimum="10pt">
	<fo:table border="0pt solid black" text-align="left" font-family="Verdana">
		<fo:table-column column-width="125mm"/>
		<fo:table-column column-width="35mm"/>
			<fo:table-body>
				<xsl:apply-templates/>
			</fo:table-body>
		</fo:table>
	</fo:block>
</xsl:template>

<xsl:template match="kandidaat">
<fo:table-row>
	<fo:table-cell padding="2pt" border="0.1pt solid black" background-color="white">
		<fo:block><xsl:value-of select="@lijstpositie"/>.&#xa0;<xsl:value-of select="@voorletters"/>&#xa0;<xsl:value-of select="@achternaam"/></fo:block>
	</fo:table-cell>
	<fo:table-cell padding="2pt" border="0.1pt solid black" background-color="white">
		<fo:block><xsl:value-of select="@aantalstemmen"/></fo:block>
	</fo:table-cell>
</fo:table-row>
</xsl:template>

</xsl:stylesheet>