<%@ taglib prefix="stripes" uri="http://stripes.sourceforge.net/stripes.tld" %>
<%@ taglib prefix="c" uri="http://java.sun.com/jsp/jstl/core" %>

<stripes:layout-render name="/WEB-INF/layout/default.jsp">
    <stripes:layout-component name="contents">
    <h1>Results</h1>
    <stripes:form beanclass="org.scantegrity.sws.action.ResultsActionBean">
    <p><i>What is shown below are unofficial results. Please go to the 
    <a href="http://www.takomaparkmd.gov/clerk/election/2009/results/index.html">
    Official Takoma Park Results page</a>. Note that the handcount did count 
    ballots that were not recognized by the scanner, and this page only shows 
    the scanner tallies. Takoma Park counts any ballot with discernable voter 
    preference on it.</i></p>
    <!--<c:if test="${actionBean.results != \"\" }"><p><i>For results with 
    write-in candidates, click <a href="results?writein=n">here.</a></i></p>
    </c:if>//-->
    <p><c:if test="${empty actionBean.results}">Please click 
    <a href="results?writein=y">here</a> for results.
    </c:if>${actionBean.results }</p>
    </stripes:form>
    <br />
    <br />
    <br />
    <br />
    <br />
    <br />
    <br />
    
    </stripes:layout-component>
</stripes:layout-render>
