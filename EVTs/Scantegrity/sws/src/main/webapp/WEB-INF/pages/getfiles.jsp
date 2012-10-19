<%@taglib prefix="stripes" uri="http://stripes.sourceforge.net/stripes.tld"%>

<stripes:layout-render name="/WEB-INF/layout/default.jsp">
    <stripes:layout-component name="contents">
    
    <h1>Election Files</h1>
    
    <stripes:form beanclass="org.scantegrity.sws.action.GetFilesActionBean">
    
    
    	${actionBean.htmlFiles}
    	
    	<br/><br/>
        <br/><br/>
        <br/><br/>
        <br/><br/>
        <br/><br/>
    
    </stripes:form>
    
        </stripes:layout-component>
</stripes:layout-render>
