<%@ taglib prefix="stripes" uri="http://stripes.sourceforge.net/stripes.tld" %>
<%@ taglib prefix="c" uri="http://java.sun.com/jsp/jstl/core" %>

<script type="text/javascript">

window.location = "checkcodes"

</script>

<stripes:layout-render name="/WEB-INF/layout/default.jsp">
    <stripes:layout-component name="contents">
    <h2>On-Line Verification Process and Survey</h2>
    
    <stripes:form beanclass="org.scantegrity.sws.action.BallotCheckActionBean">
    <c:if test="${!actionBean.ballots }">
    <p>Confirmation Numbers for the election should be available around 
    9pm on Tuesday, November 3rd 2009. Please check back at that time!</p>
    
    <br />
    <br />
    <br />
    <br />
    <br />
    <br />
    <br />
    </c:if>
    
    <c:if test="${actionBean.ballots}">
    <p>
Thank you for agreeing to participate in the on-line verification process and survey.
<br/><br/>
Before we start, we would like you to read the informed consent information below.  Informed consent refers to the voluntary choice of an individual to participate in research based on an accurate and complete understanding of its purpose, procedures, risks, benefits and alternatives.  The verification process and survey will be completely anonymous and voluntary.  We do not ask for the identity of, or identify, individuals who plan to participate in this survey.  If you have any questions, please contact the principal investigator Dr. Alan T. Sherman (email: sherman@umbc.edu).
<br/><br/>
<i>Informed Consent</i>:
<br/><br/>
You must be 18 years or older to participate in this verification process and survey.
<br/><br/>
The purpose of this study is to determine how easy the Scantegrity voting system is to use, and how well voters accept the system.  You are being asked to participate in this survey because you have participated in the April 11, 2009 or May 25, 2009, mock election and have requested to verify your vote.  The verification process and survey will take about ten minutes to complete.
<br/><br/>
There are no known risks involved in completing this survey.  There are no tangible benefits for completing the survey, but in participating you will be helping to advance research in voting technology.  
<br/><br/>
Participation is entirely voluntary;  you may at any time withdraw from participation.
<br/><br/>
All data will be anonymous.  There is no way for us to find out who you are, and your data will not be shared with other parties under any circumstances.
<br/><br/>
This study will be reviewed by the UMBC Institutional Review Board (IRB).  A representative of that Board, from the Human and Animal research Protections Office, is available to discuss the review process or my rights as a research participant.  Contact information of the Office is tele. 410 455 2737 or email HARPO@umbc.edu
<br/><br/>
After reading the consent items, please proceed to the verification process and questionnaire on the next page.
<br/><br/></p>
<div style='text-align: center'>
<a href='checkcodes'>I would like to verify my vote and possibly participate in a survey.</a><br/><br/>
<a href="index">I would like to exit now.</a><br/><br/>
</div>
 	</c:if>
</stripes:form> 
    </stripes:layout-component>
</stripes:layout-render>
