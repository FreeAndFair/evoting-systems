<%@ taglib prefix="stripes" uri="http://stripes.sourceforge.net/stripes.tld" %>

<stripes:layout-render name="/WEB-INF/layout/default.jsp">
    <stripes:layout-component name="html_head">
        <link rel="stylesheet" type="text/css" href="${pageContext['request'].contextPath}/styles/forms.css" />
    </stripes:layout-component>
    <stripes:layout-component name="contents">
    <h1>Contact Us</h1>

		<p>Please fill out the following form, and we will get back to you
		as soon as possible.</p>

		<stripes:form beanclass="org.scantegrity.sws.action.ContactActionBean" class="stylishform">
		<fieldset><legend>Contact Form</legend>
            <span style="color:red;"><stripes:errors/></span>		
		<ol>
			<li><label for="name">Name</label> <stripes:text id="name"
				name="name" style="width: 50%;" /></li>

			<li><label for="email">E-mail Address</label> 
			     <stripes:text id="email" name="email"
				    style="width: 50%;" /></li>

			<li><label for="subject">Subject</label> <stripes:text
				id="subject" name="subject" style="width: 55%;" /></li>

			<li><label for="msg">Message</label><br />

			<stripes:textarea id="msg" name="msg" cols="65" rows="20"></stripes:textarea>

			</li>
			<li>${actionBean.captchaHTML}</li>
			<li><stripes:submit name="submit" value="Send Message" /></li>
		</ol>
		</fieldset> 
		</stripes:form>


	<br />
	<br />
	</stripes:layout-component>
</stripes:layout-render>
