<%@taglib prefix="stripes" uri="http://stripes.sourceforge.net/stripes.tld"%>

<stripes:layout-render name="/WEB-INF/layout/default.jsp">
    <stripes:layout-component name="contents">
<h1>Check Codes</h1>

<p>Please input your online verification number below.  Any questions or concerns should be directed <a href="contact">here</a>.  </p>
<stripes:form beanclass="org.scantegrity.sws.action.CheckCodesActionBean">
<p>
	<label for="name">Serial:</label>
	<input type="text" id="serial" name="serial" value="${actionBean.serial}" />
	<stripes:submit name="submit" value="Submit" />
	<br /><br />
	
	<br />
	
	<stripes:errors/>
	
	${actionBean.result}
	<br/><br/>
	${actionBean.errors}
	<br/>

	<p>Please also help us by taking a <a href="https://www.surveymonkey.com/s/HLFZXRS">short survey here</a> about your voting experience.</p>
	
	
</p>
</stripes:form> 

    </stripes:layout-component>
</stripes:layout-render>
