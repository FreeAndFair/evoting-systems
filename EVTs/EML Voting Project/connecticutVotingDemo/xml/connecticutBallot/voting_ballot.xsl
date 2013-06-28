<?xml version="1.0" encoding="ISO-8859-1"?>
<xsl:stylesheet version="1.0"
xmlns:xsl="http://www.w3.org/1999/XSL/Transform"><xsl:template match="/">
  <html>
  <title><xsl:value-of select="//ballot/title"/></title>
  <head>

<style type="text/css">

    <xsl:for-each select="//ballot/column">
      <xsl:variable name="col-no" select="attribute::ID"/>
      <xsl:variable name="offset" select="attribute::offset"/>
      <xsl:for-each select="checkbox">
        <xsl:variable name="row-no" select="attribute::ID"/>
        <xsl:variable name="zindex" select="$col-no * 10 + $row-no" />
           DIV.Object-row-<xsl:value-of select="$row-no"/>-<xsl:value-of select="$col-no"/> { position:absolute; top:<xsl:value-of select="attribute::top"/>px; left:<xsl:value-of select="$offset"/>px; z-index:<xsl:value-of select="$zindex"/>; }
      </xsl:for-each>
    </xsl:for-each>

</style>

<script language="JavaScript1.2" type="text/javascript">

   function changeButton(row, col) {

      var elem = document.getElementById("row-" + col + "-" + row);
      var pos1 = elem.src.indexOf('.gif');
      pos1 = pos1 - 2;

     //alert("Getting here: " + row + ", " + col + ":" + pos1 + "-" + elem.src );

      var off = elem.src.substr(0,pos1) + "up.gif";
      var on  = elem.src.substr(0,pos1) + "on.gif";
     
      var i=1
      while (i !=<xsl:value-of select="//ballot/@maxRows"/>)
        {
          elem = document.getElementById("row-" + i + "-" + row);
	       if (elem != null) {

             if (i == col) {
              elem.src = on;
              }
             else {
              elem.src = off;
              }
          }

          i = i + 1;
        }
	

      switch(row)
      {
      <xsl:for-each select="//ballot/column">
      case <xsl:value-of select="attribute::ID"/>:
     // alert(<xsl:value-of select="attribute::ID"/>);
     // alert(row +'-'+ col);
      document.voterForm.voted<xsl:value-of select="attribute::ID"/>.value=col;
      break
      </xsl:for-each>
      default:
       alert("ERROR: Column out of range: " + col)
      }

     // alert("Ending on: " + row + "," + col);
    }

     function reVote()
     {
      <xsl:for-each select="//ballot/column">
      document.voterForm.voted<xsl:value-of select="attribute::ID"/>.value="";
      </xsl:for-each>
      history.go();
     }
    function completeVote()
	   {
	   
	        var voted1=0,voted2=0,voted3=0,voted4=0,voted5=0,voted6=0,voted7=0,voted8=0,voted9=0,voted10=0,voted11=0;
	        
	        voted1=document.getElementById("voted1").value;
	        voted2=document.getElementById("voted2").value;
	        voted3=document.getElementById("voted3").value;
	        voted4=document.getElementById("voted4").value;
	        voted5=document.getElementById("voted5").value;
	        voted6=document.getElementById("voted6").value;
	        voted7=document.getElementById("voted7").value;
	        voted8=document.getElementById("voted8").value;
	        voted9=document.getElementById("voted9").value;
	        voted10=document.getElementById("voted10").value;
	        voted11=document.getElementById("voted11").value;
	        
	   
	         document.forms[0].pageAction.value="voteComplete";
  	         var d = new Date()
		     var t = d.getTime()
		     document.forms[0].transactionID.value=t;
		     var transactionID;
			 transactionID=document.forms[0].transactionID.value;                       
             document.forms[0].submit();
        
	   }
   </script>
  </head>
  <body>
   <form name="voterForm" action="/connecticutVotingDemo/actions/scanvoter.do">

    <xsl:element name="img">
        <xsl:attribute name="src"><xsl:value-of select="//ballot/image"/></xsl:attribute>
        <xsl:attribute name="alt"> </xsl:attribute>
    </xsl:element>

    <xsl:for-each select="//ballot/column">
      <xsl:variable name="col-no" select="attribute::ID"/>
      <xsl:variable name="offset" select="attribute::offset"/>
      <xsl:for-each select="checkbox">
        <xsl:variable name="row-no" select="attribute::ID"/>
        <xsl:element name="div">
         <xsl:attribute name="class">Object-row-<xsl:value-of select="$row-no"/>-<xsl:value-of select="$col-no"/></xsl:attribute>
         <xsl:element name="img">
          <xsl:attribute name="id">row-<xsl:value-of select="$row-no"/>-<xsl:value-of select="$col-no"/></xsl:attribute>
          <xsl:attribute name="onclick">changeButton(<xsl:value-of select="$col-no"/>,<xsl:value-of select="$row-no"/>)</xsl:attribute>
          <xsl:attribute name="src">http://openvotingsolutions.info/connecticutVotingDemo/xml/connecticutBallot/button-up.gif</xsl:attribute>
          <xsl:attribute name="border">0</xsl:attribute>
          <xsl:attribute name="alt"> </xsl:attribute>
         </xsl:element>
        </xsl:element>
      </xsl:for-each>
    </xsl:for-each>

    <xsl:for-each select="//ballot/column">
      <xsl:element name="INPUT">
        <xsl:attribute name="TYPE">HIDDEN</xsl:attribute>
        <xsl:attribute name="NAME">voted<xsl:value-of select="attribute::ID"/></xsl:attribute>
      </xsl:element>
    </xsl:for-each>
   <xsl:element name="INPUT">
            <xsl:attribute name="TYPE">HIDDEN</xsl:attribute>
            <xsl:attribute name="NAME">pageAction</xsl:attribute>
            <xsl:attribute name="VALUE"></xsl:attribute>
    </xsl:element>
    <xsl:element name="INPUT">
            <xsl:attribute name="TYPE">HIDDEN</xsl:attribute>
            <xsl:attribute name="NAME">transactionID</xsl:attribute>
            <xsl:attribute name="VALUE"></xsl:attribute>
    </xsl:element>
    <xsl:element name="br"/>
    <button type="reset" onClick="reVote()">Restart Voting</button>
    <button type="submit" onClick="completeVote()">Complete Voting</button>

    </form>
  </body>
  </html>
</xsl:template></xsl:stylesheet>
