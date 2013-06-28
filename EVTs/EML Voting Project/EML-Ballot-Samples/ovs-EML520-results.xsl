<?xml version="1.0" encoding="ISO-8859-1"?>
<xsl:stylesheet version="1.0"
xmlns:xsl="http://www.w3.org/1999/XSL/Transform"><xsl:template match="/">
  <html>
  <head>
  <title>Election Results</title>
  </head>
  <body>
    <h2>Election Results</h2>
    <h2><xsl:value-of select="//ElectionIdentifier/@Id"/></h2>
    <h2><xsl:value-of select="//ContestIdentifier/@Id"/></h2>
    <hr/>
    <table border="0" width="100%">
      <tr bgcolor="#9acd32">
        <th align="left" width="40%">Candidate</th>
        <th align="left" width="40%">Affilation</th>
        <th align="left" width="20%">Votes</th>
      </tr>
      <xsl:for-each select="//Contest/Selection">
      <tr>
        <td align="left" width="40%"><xsl:value-of select="CandidateIdentifier/CandidateName" /></td>
        <td align="left" width="40%"><xsl:value-of select="Affiliation/AffiliationIdentifier/RegisteredName" /></td>
        <td align="left" width="20%"><xsl:value-of select="Votes" /></td>
      </tr>
      </xsl:for-each>
  </table>
  </body>
  </html>
</xsl:template></xsl:stylesheet>
