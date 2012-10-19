<%@ taglib prefix="stripes" uri="http://stripes.sourceforge.net/stripes.tld" %>
<stripes:layout-render name="/WEB-INF/layout/default.jsp">
    <stripes:layout-component name="contents">
   <h1>Oops!</h1>
   <p>We are sorry, the page you requested was not found!</p>
    <p><b>Options: </b></p> 
    <ul>
        <li><a href="${pageContext.request.contextPath}/index">Home Page</a></li>
        <li><a href="${pageContext.request.contextPath}/contact">Contact us about the problem</a></li>
    </ul>
    </stripes:layout-component>
</stripes:layout-render>
