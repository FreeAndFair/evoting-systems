<?xml version="1.0" encoding="ISO-8859-1"?>
<xsl:stylesheet version="1.0"
xmlns:xsl="http://www.w3.org/1999/XSL/Transform"><xsl:template match="/">
  <html>
  <title>Italian Election System</title>
  <head>
     <script language="JavaScript1.2">
           function printVotedBallot() {
             window.print();
             window.close();
           }
     </script>
  </head>   
  <body >
    <h2>Senate Election</h2>
<!--    <h2><xsl:value-of select="//ballot/@version"/></h2>
    <h2><xsl:value-of select="//ballot/@ID"/></h2>
-->
    <br/>
    <hr/>
    <br/>
    <xsl:for-each select="//row">
      <xsl:variable name="row-no" select="attribute::node()"/>
      <table>
      <tr>
       <xsl:for-each select="child::node()">       	   
         <xsl:if  test="attribute::node()" >
         <td>		
	   <xsl:if test="node()= 0">
 	     <xsl:element name="img">
	      <xsl:attribute name="src">/home/ovsadmin/italyVoting/xml/ballots/images/Row-Box-Print.jpg</xsl:attribute>
             </xsl:element>
 	   </xsl:if>	 
           <xsl:if test="node()= 1">
 	     <xsl:element name="img">
	      <xsl:attribute name="src">/home/ovsadmin/italyVoting/xml/ballots/images/Row-<xsl:value-of select="$row-no"/>-Item-<xsl:value-of select="attribute::node()" />-selected.jpg</xsl:attribute>
             </xsl:element>
	   </xsl:if>	 
	 </td>
         </xsl:if>
       </xsl:for-each>
      </tr>
      </table>
    </xsl:for-each>
    <br/>
    <hr/>
  </body>
  </html>
</xsl:template></xsl:stylesheet>
