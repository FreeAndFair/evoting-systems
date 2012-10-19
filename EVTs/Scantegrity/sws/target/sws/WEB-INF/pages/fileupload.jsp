<%@taglib prefix="stripes" uri="http://stripes.sourceforge.net/stripes.tld"%>
<stripes:layout-render name="/WEB-INF/layout/default.jsp">
    <stripes:layout-component name="contents">


<h1>File Upload</h1>

<stripes:form beanclass="org.scantegrity.sws.action.FileuploadActionBean">
<div>
	<stripes:file name="file" /></br>
	<label for="name">Style ID (for codes only):</label>
	<input type="text" id="styleId" name="styleId" value="${actionBean.styleId}" />
	<stripes:submit name="submit" value="Upload" />
	<br /><br />
	
	<br />
	
	<stripes:errors/>
	
	<br/><br/>
	${actionBean.result}
	<br/><br/>
	${actionBean.errors}
	  </div>
</stripes:form> 

    </stripes:layout-component>
</stripes:layout-render>
