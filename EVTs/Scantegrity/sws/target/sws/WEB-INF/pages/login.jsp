<%@taglib prefix="stripes" uri="http://stripes.sourceforge.net/stripes.tld"%>

<stripes:layout-render name="/WEB-INF/layout/default.jsp">
    <stripes:layout-component name="contents">
<h1>Login</h1>

<p>The page you were trying to access is restricted, please enter your user name and password below:</p>
<stripes:form beanclass="org.scantegrity.sws.action.LoginActionBean">

	<label for="username">User Name:</label>
	<input type="text" id="username" name="username" value="${actionBean.username}" /> <br/>
	<label for="password">Password:</label>
	<input type="password" id="password" name="password" /> <br/>
	<stripes:submit name="submit" value="Submit" />
	<br /><br />
	
	<br />
	
	<stripes:errors/>
	
	<br/><br/>
	${actionBean.errors}
	
</stripes:form> 

    </stripes:layout-component>
</stripes:layout-render>
