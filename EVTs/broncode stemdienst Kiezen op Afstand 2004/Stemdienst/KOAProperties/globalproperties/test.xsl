<?xml version="1.0"?>

<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform" xmlns:fo="http://www.w3.org/1999/XSL/Format" exclude-result-prefixes="fo">
<xsl:output method="xml" version="1.0" omit-xml-declaration="no" indent="yes"/>

<!-- FO root -->
<xsl:template match="TABLE">
	<fo:root xmlns:fo="http://www.w3.org/1999/XSL/Format">
		<fo:layout-master-set>
			<fo:simple-page-master master-name="simpleA4" page-height="29.7cm" page-width="21cm" margin-top="2cm" margin-bottom="2cm" margin-left="2cm" margin-right="2cm">
			<fo:region-body/>
			</fo:simple-page-master>
		</fo:layout-master-set>
		<fo:page-sequence master-reference="simpleA4">
			<fo:flow flow-name="xsl-region-body">
				<fo:block font-size="16pt"><xsl:value-of select="@NAME"/></fo:block>
			<fo:block>
				<xsl:apply-templates/>
			</fo:block>
			</fo:flow>
		</fo:page-sequence>
	</fo:root>
</xsl:template>


<!-- END OF ROOT -->

<xsl:template match="ROW">
	<xsl:value-of select="@ROW_ID"/>-<xsl:value-of select="@MESSAGE"/>
</xsl:template>

</xsl:stylesheet>