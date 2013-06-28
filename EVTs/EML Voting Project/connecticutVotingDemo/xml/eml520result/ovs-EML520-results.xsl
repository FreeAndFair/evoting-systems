<?xml version="1.0" encoding="ISO-8859-1"?>
<xsl:stylesheet version="1.0"
xmlns:xsl="http://www.w3.org/1999/XSL/Transform"><xsl:template match="/">
  <html>
  <body>
    <xsl:element name="img">
    	 <xsl:attribute name="src">/connecticutVotingDemo/web/images/flag.jpg</xsl:attribute>
    	 <xsl:attribute name="width">30</xsl:attribute>
    	 <xsl:attribute name="height">30</xsl:attribute>
    	 <xsl:attribute name="border">0</xsl:attribute>
    	 <xsl:attribute name="alt">Election System</xsl:attribute>
    </xsl:element> - Election Results

   <xsl:for-each select="//Election/Contest">

    <h2><xsl:value-of select="ElectionIdentifier/@Id"/></h2>
    <h2><xsl:value-of select="ContestIdentifier/@Id"/></h2>

    <table border="0" width="100%">
      <tr bgcolor="#9acd32">
        <th align="left" width="40%">Candidate</th>
        <th align="left" width="40%">Affilation</th>
        <th align="left" width="20%">Votes</th>
      </tr>
      <xsl:for-each select="Selection">
      <xsl:if test="CandidateIdentifier/CandidateName != 'NONE'">
       <tr>
        <td align="left" width="40%"><xsl:value-of select="CandidateIdentifier/CandidateName" /></td>
        <td align="left" width="40%"><xsl:value-of select="Affiliation/AffiliationIdentifier/RegisteredName" /></td>
         <xsl:if test="Votes &gt; 0">
          <td align="left" width="20%"><xsl:value-of select="Votes" /></td>
         </xsl:if>
         <xsl:if test="Votes &lt; 1">
          <td align="left" width="20%"></td>
         </xsl:if>
       </tr>
      </xsl:if>
      </xsl:for-each>
   </table>
    <hr/>
  </xsl:for-each>

<center><a href="/connecticutVotingDemo//actions/counting.do?countingType=done">
Home Page</a></center>
  </body>
  </html>
</xsl:template></xsl:stylesheet>
