<%@ taglib uri="/WEB-INF/struts-bean.tld" prefix="bean" %>
<%@ taglib uri="/WEB-INF/struts-html.tld" prefix="html" %>
<%@ taglib uri="/WEB-INF/struts-logic.tld" prefix="logic" %>
<%@ taglib uri="/WEB-INF/struts-tiles.tld" prefix="tiles" %>
<%@ page import="org.apache.struts.action.ActionMessages" %>
<%@ page import="java.util.*" %>
<script type="text/javascript">
function votingComplete(URL) {
 window.print(2);
 window.location.href=URL;
 return;
}
function changeSrc(imgName,order,img_src)
  {

  document.voterForm.lastClickedName.value=imgName;
  if(order=="1") {
  	document.voterForm.voted.value="1";
  	document.voterForm.lastClickedSrc.value=img_src+"1.jpg";
       document.getElementById("img2").src=img_src+"2_bk.jpg";
       document.getElementById("img3").src=img_src+"3_bk.jpg";
     }
     if(order=="2") {
     document.voterForm.voted.value="2";
     document.voterForm.lastClickedSrc.value=img_src+"2.jpg";
        document.getElementById("img1").src=img_src+"1_bk.jpg";
        document.getElementById("img3").src=img_src+"2_bk.jpg";
     }
     if(order=="3") {
     document.voterForm.voted.value="3";
     document.voterForm.lastClickedSrc.value=img_src+"3.jpg";
	         document.getElementById("img1").src=img_src+"1_bk.jpg";
	         document.getElementById("img2").src=img_src+"2_bk.jpg";
     }
  }
function movepic(img_name,img_src) {
	document[img_name].src=img_src;
}
function changeIMG(img_name,img_src) {
    lastClickedName=document.voterForm.lastClickedName.value;
    lastClickedSrc=document.voterForm.lastClickedSrc.value;
    if((lastClickedName.length>0) && (lastClickedSrc.length>0)) {
    	document[img_name].src=img_src;
    	document[lastClickedName].src=lastClickedSrc;
    }

}
</script>

<%
    // This variable will be equal to the URL pattern of the web application server.
    String contextPath = request.getContextPath(); 
    String imageSrc = contextPath+"/web/images/ballot/";
    
%>
   <form method="post" name="voterForm" action="<%=request.getContextPath()%>/scanVoter.do" >
  <img name="img1" id="img1" src="<%=imageSrc%>1.jpg" onclick="changeSrc(this.name,'1','<%=imageSrc%>')"
  		onmouseover="movepic('img1','<%=imageSrc%>1.jpg')"
  		onmouseout="changeIMG('img1','<%=imageSrc%>1_bk.jpg')"/>
  <img name="img2" id="img2" src="<%=imageSrc%>2.jpg" onclick="changeSrc(this.name,'2','<%=imageSrc%>')"
  		onmouseover="movepic('img2','<%=imageSrc%>2.jpg')"
  		onmouseout="changeIMG('img2','<%=imageSrc%>2_bk.jpg')"/>
  <img name="img3" id="img3" src="<%=imageSrc%>3.jpg" onclick="changeSrc(this.name,'3','<%=imageSrc%>')"
  		onmouseover="movepic('img3','<%=imageSrc%>3.jpg')"
  		onmouseout="changeIMG('img3','<%=imageSrc%>3_bk.jpg')"/>
  <input type="hidden" name="lastClickedName" value"">
  <input type="hidden" name="lastClickedSrc" value"">
  <input type="hidden" name="voted" value"">
  <br><br>
<input type=reset name=reset value="Restart Voting" onClick="history.go()">
<input type=button name=print value="Complete Voting" onClick="votingComplete('<%=contextPath%>/scanVoter.do')">
 
   </form> 