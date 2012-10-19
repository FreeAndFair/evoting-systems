<%@ taglib prefix="stripes" uri="http://stripes.sourceforge.net/stripes.tld" %>
<%@ taglib prefix="c" uri="http://java.sun.com/jsp/jstl/core" %>

<stripes:layout-render name="/WEB-INF/layout/default.jsp">
    <stripes:layout-component name="contents">
    <h1>Admin Panel</h1>
    <p>
    	<a href="fileupload">Upload files</a><br/><br/>
    	<a href="useradd">Manage users</a>
    	<stripes:form beanclass="org.scantegrity.sws.action.AdminActionBean">
    		<stripes:submit name="deleteDatabase" value="Delete Database" />
    	</stripes:form>
    	<stripes:form beanclass="org.scantegrity.sws.action.AdminActionBean">
    		<stripes:submit name="logout" value="Logout" />
    	</stripes:form>
    </p>
    <br />
    <br />
    <br />
    <br />
    <br />
    <br />
    <br />
    
    </stripes:layout-component>
</stripes:layout-render>
