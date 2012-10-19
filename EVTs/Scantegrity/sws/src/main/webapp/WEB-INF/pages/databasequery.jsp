<%@taglib prefix="stripes" uri="http://stripes.sourceforge.net/stripes.tld"%>

<stripes:layout-render name="/WEB-INF/layout/default.jsp">
    <stripes:layout-component name="contents">
<h1>Database Query</h1>

<p>Input database query text below</p>
<stripes:form beanclass="org.scantegrity.sws.action.DatabaseQueryActionBean">
<p>
	<label for="name">Query:</label>
	<input type="text" id="query" name="query" value="${actionBean.query}" />
	<stripes:submit name="submit" value="Submit" />
	<br /><br />
	
	<br />
	
	<stripes:errors/>
	${actionBean.results}
	<br/>
	
</p>
</stripes:form> 

    </stripes:layout-component>
</stripes:layout-render>
