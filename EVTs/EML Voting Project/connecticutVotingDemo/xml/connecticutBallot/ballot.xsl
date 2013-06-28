<?xml version="1.0" encoding="ISO-8859-1"?>
<xsl:stylesheet version="1.0"
xmlns:xsl="http://www.w3.org/1999/XSL/Transform"><xsl:template match="/">
  <html>
  <head>
   <title>Connecticut Election System</title>
  </head>
  <body >
    <h2>Connecticut State Election</h2>
    <h3>Ballot <font color="blue"><xsl:value-of select="//ballot/@ID"/></font></h3>
    <br/>
    <hr/>
    <br/>
    <xsl:for-each select="//column">
      <table>
      <tr>
          <xsl:variable name="col-no" select="attribute::node()"/>
          <td width="12%"><p>Col: <xsl:value-of select="$col-no"/> &#187;<br/> <br/><font size="1">&#183;</font></p>
          </td>
       <xsl:for-each select="checkbox">
         <td>		
	   <xsl:if test="node()= 0">
 	     <xsl:element name="img">
	      <xsl:attribute name="src">http://openvotingsolutions.info/connecticutVotingDemo/xml/connecticutBallot/button-up.gif</xsl:attribute>
             </xsl:element>
 	   </xsl:if>	
           <xsl:if test="node()= 1">
 	     <xsl:element name="img">
	      <xsl:attribute name="src">http://openvotingsolutions.info/connecticutVotingDemo/xml/connecticutBallot/button-on.gif</xsl:attribute>
             </xsl:element>
	   </xsl:if>	
	 </td>
       </xsl:for-each>
      </tr>
      </table>
    </xsl:for-each>
    <br/>
    <hr/>
  </body>
  </html>
</xsl:template></xsl:stylesheet>
