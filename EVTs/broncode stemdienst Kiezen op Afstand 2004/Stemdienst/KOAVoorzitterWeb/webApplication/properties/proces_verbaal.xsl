<?xml version="1.0"?>

<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform" xmlns:fo="http://www.w3.org/1999/XSL/Format" exclude-result-prefixes="fo">
<xsl:output method="xml" version="1.0" omit-xml-declaration="no" indent="yes"/>

<!-- FO root -->
<xsl:template match="/REPORT">
	<fo:root xmlns:fo="http://www.w3.org/1999/XSL/Format">
		<fo:layout-master-set>
			<fo:simple-page-master master-name="simpleA4" page-height="21cm" page-width="29.7cm" margin-top="2cm" margin-bottom="2cm" margin-left="2cm" margin-right="2cm">
			<fo:region-body/>
			</fo:simple-page-master>
		</fo:layout-master-set>
		<fo:page-sequence master-reference="simpleA4">
			<fo:flow flow-name="xsl-region-body">
			<!--fo:block font-size="16pt" text-align="center" space-after.optimum="10pt">
				Logbestand
			</fo:block> -->
			<xsl:apply-templates select="PAGETITLE" />
			<xsl:apply-templates select="GLOBAAL" />
<!--			<xsl:apply-templates select="KIESKRINGEN" /> -->
<!--			<xsl:apply-templates select="KIESKRING" /> -->
			<xsl:apply-templates select="DATE" />			
			<xsl:apply-templates select="TABLE" />
<!--			<xsl:apply-templates select="ROW" /> -->
			</fo:flow>
		</fo:page-sequence>
	</fo:root>
</xsl:template>


<!-- END OF ROOT -->

<!-- display pagetitle -->
<xsl:template name="pagetitle" match="REPORT/PAGETITLE">
	<fo:block font-size="16pt" text-align="center" space-after.optimum="10pt">
		<xsl:value-of select="@TITLE" />
	</fo:block> 
</xsl:template>

<xsl:template name="globaal" match="REPORT/GLOBAAL">
	<fo:block font-size="12pt" space-after.optimum="15pt">
		<fo:table border="0pt solid black" text-align="left">
			<fo:table-column column-width="86mm"/>
			<fo:table-column column-width="178mm"/>
			<fo:table-body>
				<fo:table-row>
					<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
						<fo:block>
							Stembureau
						</fo:block>
					</fo:table-cell>
					<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
						<fo:block>
							<xsl:value-of select="@STEMBUREAU" />
						</fo:block>
					</fo:table-cell>
				</fo:table-row>
				<fo:table-row>
					<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
						<fo:block>
							Omschrijving verkiezing
						</fo:block>
					</fo:table-cell>
					<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
						<fo:block>
							<xsl:value-of select="@VERKIEZING" />
						</fo:block>
					</fo:table-cell>
				</fo:table-row>
				<fo:table-row>
					<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
						<fo:block>
							Start periode 
						</fo:block>
					</fo:table-cell>
					<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
						<fo:block>
							<xsl:value-of select="@PERIODE_START" />
						</fo:block>
					</fo:table-cell>
				</fo:table-row>
				<fo:table-row>
					<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
						<fo:block>
							Einde periode 
						</fo:block>
					</fo:table-cell>
					<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
						<fo:block>
							<xsl:value-of select="@PERIODE_EIND" />
						</fo:block>
					</fo:table-cell>
				</fo:table-row>
				<fo:table-row>
					<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
						<fo:block>
							Huidige status
						</fo:block>
					</fo:table-cell>
					<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
						<fo:block>
							<xsl:value-of select="@STATE" />
						</fo:block>
					</fo:table-cell>
				</fo:table-row>
			</fo:table-body>
		</fo:table>
	</fo:block>
	<xsl:apply-templates select="KIESKRINGEN" />
</xsl:template>

<xsl:template name="kieskringen" match="REPORT/GLOBAAL/KIESKRINGEN">
	<fo:block font-size="14pt" space-after.optimum="10pt">
		Kieskringen
	</fo:block>
	<fo:block font-size="12pt" space-after.optimum="15pt">
		<fo:table border="0pt solid black" text-align="left">
			<fo:table-column column-width="86mm"/>
			<fo:table-column column-width="178mm"/>
			<fo:table-body>
				<fo:table-row>
					<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
						<fo:block font-size="10pt">
							Naam
						</fo:block>
					</fo:table-cell>
					<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
						<fo:block font-size="10pt">
							Nummer
						</fo:block>
					</fo:table-cell>
				</fo:table-row>
				<xsl:apply-templates select="KIESKRING" />
			</fo:table-body>
		</fo:table>
	</fo:block>
</xsl:template>

<xsl:template name="kieskring" match="REPORT/GLOBAAL/KIESKRINGEN/KIESKRING">
	<fo:table-row>
		<fo:table-cell padding="1pt" border="0pt solid black">
			<fo:block font-size="8pt">
				<xsl:value-of select="@NAAM" />
			</fo:block>
		</fo:table-cell>
		<fo:table-cell padding="1pt" border="0pt solid black">
			<fo:block font-size="8pt">
				<xsl:value-of select="@NUMMER" />
			</fo:block>
		</fo:table-cell>
	</fo:table-row>
</xsl:template>



<xsl:template name="date" match="REPORT/DATE">
	<fo:block font-size="14pt" space-after.optimum="10pt">
		Auditlog
	</fo:block>

	<fo:block font-size="12pt" space-after.optimum="10pt">
		Alle meldingen van <xsl:value-of select="@START" /> tot <xsl:value-of select="@END" />
	</fo:block>
</xsl:template>


<xsl:template name="TABLE" match="REPORT/TABLE">
	<fo:block font-size="12pt" space-after.optimum="15pt">
		<fo:table border="0pt solid black" text-align="left">
			<fo:table-column column-width="13mm"/>
			<fo:table-column column-width="22mm"/>			
			<fo:table-column column-width="8mm"/>
			<fo:table-column column-width="34mm"/>
			<fo:table-column column-width="187mm"/>			
			<fo:table-body>
				<fo:table-row>
					<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
						<fo:block font-size="9pt">
							Nummer
						</fo:block>
					</fo:table-cell>
					<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
						<fo:block font-size="9pt">
							Tijdstip
						</fo:block>
					</fo:table-cell>
					<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
						<fo:block font-size="9pt">
							Type
						</fo:block>
					</fo:table-cell>
					<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
						<fo:block font-size="9pt">
							Initiator
						</fo:block>
					</fo:table-cell>
					<fo:table-cell padding="2pt" border="0pt solid black" background-color="silver">
						<fo:block font-size="9pt">
							Melding
						</fo:block>
					</fo:table-cell>
				</fo:table-row>
				<xsl:apply-templates select="ROW" />
			</fo:table-body>
		</fo:table>
	</fo:block>
</xsl:template>

<xsl:template name="row" match="REPORT/TABLE/ROW">
	<fo:table-row>
		<fo:table-cell padding="1pt" border="0pt solid black">
			<fo:block font-size="9pt">
				<xsl:value-of select="@ROW_ID" />
			</fo:block>
		</fo:table-cell>
		<fo:table-cell padding="1pt" border="0pt solid black">
			<fo:block font-size="9pt">
				<xsl:value-of select="@TIMESTAMP" />
			</fo:block>
		</fo:table-cell>
		<fo:table-cell padding="1pt" border="0pt solid black">
			<fo:block font-size="9pt">
				<xsl:value-of select="@TYPE" />
			</fo:block>
		</fo:table-cell>
		<fo:table-cell padding="1pt" border="0pt solid black">
			<fo:block font-size="9pt">
				<xsl:value-of select="@INITIATOR" />
			</fo:block>
		</fo:table-cell>
		<fo:table-cell padding="1pt" border="0pt solid black">
			<fo:block font-size="9pt">
				<xsl:value-of select="@MESSAGE" />
			</fo:block>
		</fo:table-cell>
	</fo:table-row>		
</xsl:template>


<xsl:template match="GLOBAAL"></xsl:template>
<xsl:template match="KIESKRINGEN"></xsl:template>
<xsl:template match="KIESKRING"></xsl:template>
<xsl:template match="DATE"></xsl:template>
<xsl:template match="TABLE"></xsl:template>
<xsl:template match="ROW"></xsl:template>

</xsl:stylesheet>