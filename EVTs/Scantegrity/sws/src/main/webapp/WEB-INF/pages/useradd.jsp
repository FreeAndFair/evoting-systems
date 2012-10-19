<%@taglib prefix="stripes" uri="http://stripes.sourceforge.net/stripes.tld"%>
<%@ taglib prefix="c" uri="http://java.sun.com/jsp/jstl/core" %>

<stripes:layout-render name="/WEB-INF/layout/default.jsp">
    <stripes:layout-component name="contents">
<h1>User Management</h1>

<p>Enter user name and password below to add new user:</p>
<stripes:form beanclass="org.scantegrity.sws.action.UserAddActionBean">

	<label for="username">User Name:</label>
	<input type="text" id="username" name="username" value="${actionBean.username}" /> <br/>
	<label for="password">Password:</label>
	<input type="password" id="password" name="password" /> <br/>
	<stripes:submit name="addUser" value="Submit" />
	<br />
	
	<br />
	
	<stripes:errors/>
	${actionBean.errors}
	
</stripes:form> 

<stripes:form beanclass="org.scantegrity.sws.action.LoginActionBean">
<table style="width: 80%">
<tr><th>User Name</th><th></th></tr>
	<c:forEach items="${actionBean.allUsers}" var="user">
		<tr>
			<td>${user}</td>
			<td>
				<stripes:link href="/useradd" event="deleteUser">
					Delete 
					<stripes:param name="target" value="${user}" />
				</stripes:link>
			</td>
		</tr>
	</c:forEach>
</table>
</stripes:form>

    </stripes:layout-component>
</stripes:layout-render>
