<?xml version="1.0" encoding="ISO-8859-1"?>
<xsl:stylesheet version="1.0"
xmlns:xsl="http://www.w3.org/1999/XSL/Transform"><xsl:template match="/">
  <html>
  <title>Italian Election System</title>
  <head>
     <script language="JavaScript1.2">
           function changeSrcRow1(imgName,order,row) {
	    if(row==1) {	
	     var voted1 = document.forms[0].voted1.value;	   
	     if(voted1.length ==0) {
	        document.forms[0].voted1.value=order;
	      //alert("Selected image is " + imgName);
		var i=1
		while (i !=9)
		{
		  if(order !="1"+i) {	    
		    document.getElementById("1"+i).src="http://openvotingsolutions.info/iTalyVotingDemo/xml/images/Row-1-Item-"+i+"-off.jpg";
		  }		 	
		  i=i+1;
		}
	      }
            }
	    if(row==2) {	
	     var voted2 = document.forms[0].voted2.value;	   
	     if(voted2.length ==0) {
	        document.forms[0].voted2.value=order;
	      //alert("Selected image is " + imgName);
		var i=1
		while (i !=4)
		{
		  if(order !="2"+i) {	    
		    document.getElementById("2"+i).src="http://openvotingsolutions.info/iTalyVotingDemo/xml/images/Row-2-Item-"+i+"-off.jpg";
		  }		 	
		  i=i+1;
		}
	      }
            }
	   if(row==3) {	
	     var voted3 = document.forms[0].voted3.value;	   
	     if(voted3.length ==0) {
	        document.forms[0].voted3.value=order;
		var i=1
		while (i !=8)
		{
		  if(order !="3"+i) {	    
		    document.getElementById("3"+i).src="http://openvotingsolutions.info/iTalyVotingDemo/xml/images/Row-3-Item-"+i+"-off.jpg";
		  }		 	
		  i=i+1;
		}
	      }
            }
           }
	   function reVote()
	   {
  	     document.forms[0].voted1.value="";
  	     document.forms[0].voted2.value="";
  	     document.forms[0].voted3.value="";	   
	     history.go();
	   }	
       function completeVote()
	   {
	     var voted1;
	     var voted2;
	     var voted3;	     
  	     voted1 = document.forms[0].voted1.value;
  	     voted2 = document.forms[0].voted2.value;
  	     voted3 = document.forms[0].voted3.value;  	    
  	     var voted=0;
  	     if(voted1.length!=0) {
  	        if(voted2.length!=0) { 
  	         if(voted3.length!=0) { 
  	         voted=1;
  	         }
  	        }
  	      }
  	      if(voted==1) {
  	      document.forms[0].pageAction.value="voteComplete";
  	        var d = new Date()
		    var t = d.getTime()
		    document.forms[0].transactionID.value=t;
		    var transactionID;
			transactionID=document.forms[0].transactionID.value;
           	
           //	var newContent;
           //     newContent="/ItalyVoting/xml/ballots/ballot_"+transactionID+".xml";
           //     window.open(newContent, 'nextWin', 'right=0, top=20,width=825,height=550');                
             }  
             else {
              alert('Please complete the voting...!!!');
              document.forms[0].pageAction.value="voteNotComplete";
              document.forms[0].voted1.value="";
              document.forms[0].voted2.value="";
              document.forms[0].voted3.value="";
              document.forms[0].transactionID.value="";
              	document.forms[0].submit();
              //history.go();
              //document.forms[0].action="http://openvotingsolutions.info/iTalyVotingDemo/actions/scanvoter.do?pageAction=success";
             }
             document.forms[0].submit();
	   }
      </script>
  </head>
  <body>
  <form action="http://openvotingsolutions.info/iTalyVotingDemo/actions/scanvoter.do" >
    <h2>Senate Election</h2>
   <!-- <h2><xsl:value-of select="//ballot/@version"/></h2>
    <h2><xsl:value-of select="//ballot/@ID"/></h2>
    -->
    <hr/>
    <br/>
    <xsl:for-each select="//row">
      <xsl:variable name="row-no" select="attribute::node()"/>
      <table>
      <tr>
       <xsl:for-each select="child::node()">       	   
         <xsl:if  test="attribute::node()" >
         <td>			  
 	     <xsl:element name="img">
		<xsl:attribute name="id"><xsl:value-of select="$row-no"/><xsl:value-of select="attribute::node()"/>
		</xsl:attribute>
		<xsl:attribute name="src">http://openvotingsolutions.info/iTalyVotingDemo/xml/images/Row-<xsl:value-of select="$row-no"/>-Item-<xsl:value-of select="attribute::node()"/>-selected.jpg</xsl:attribute>		      
<!--		      <xsl:if test="$row-no= 1">		       -->
	      	        <xsl:attribute name="onclick">changeSrcRow1('Row-'+<xsl:value-of select="$row-no"/>+'-Item-'+<xsl:value-of select="attribute::node()"/>+'-selected.jpg',<xsl:value-of select="$row-no"/><xsl:value-of select="attribute::node()"/>,<xsl:value-of select="$row-no"/>)  		      
		        </xsl:attribute>	      	  
<!--		      </xsl:if> -->
             </xsl:element>
	 </td>
         </xsl:if>
       </xsl:for-each>
      </tr>
      </table>
    </xsl:for-each>
    <xsl:element name="INPUT">
        <xsl:attribute name="TYPE">HIDDEN</xsl:attribute>
        <xsl:attribute name="NAME">voted1</xsl:attribute>
        <xsl:attribute name="VALUE"></xsl:attribute>
    </xsl:element>
    <xsl:element name="INPUT">
        <xsl:attribute name="TYPE">HIDDEN</xsl:attribute>
        <xsl:attribute name="NAME">voted2</xsl:attribute>
        <xsl:attribute name="VALUE"></xsl:attribute>
    </xsl:element>
    <xsl:element name="INPUT">
        <xsl:attribute name="TYPE">HIDDEN</xsl:attribute>
        <xsl:attribute name="NAME">voted3</xsl:attribute>
        <xsl:attribute name="VALUE"></xsl:attribute>
    </xsl:element>
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
    <xsl:element name="hr"/>
    <xsl:element name="br"/>
    <button type="reset" onClick="reVote()">Restart Voting</button>  
    <button type="submit" onClick="completeVote()">Complete Voting</button>  
    </form>
  </body>
  </html>
</xsl:template></xsl:stylesheet>
