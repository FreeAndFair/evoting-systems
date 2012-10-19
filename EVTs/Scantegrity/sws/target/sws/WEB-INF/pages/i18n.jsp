
<%@taglib prefix="s" uri="http://stripes.sourceforge.net/stripes.tld"%>


<h1>Scantegrity Internationalization Test</h1>
The selected name and language, or your Browser's name and default language, 
should appear in the text below:

<h3>
			<fmt:message key="greeting">
				<fmt:param>${actionBean.name}</fmt:param>
			</fmt:message>
			<fmt:message key="return"/>
</h3>

<s:form beanclass="action.i18nActionBean">
<fieldset>
    <legend>Change Locale Settings</legend>
	<ol>
	    <li>
	        <label for="name">Name</label>
	        <input type="text" id="name" name="name" value="${sessionScope.name}" /><br />
	    </li>
	    <li>
	        <label for="locale">Locale</label>
	        <s:select id="locale" name="locale">
				 <s:option value="en">English (en)</s:option>
				 <s:option value="fr">French (fr)</s:option>
	    		 <s:option value="de">German (de)</s:option>
				 <s:option value="es">Spanish (es)</s:option>
	        </s:select>
	    </li>
	</ol>
	<br />
	<s:submit name="submit" value="Change Locale" />
</fieldset>
</s:form>

<br /><br />
<h3>Other Info</h3>

<p>Your browser's detected locale was: ${header['Accept-Language']}</p>
<p>Your browser's detected name was: ${header['User-Agent']}
<p>The current set locale is: ${actionBean.locale}
<br /><br />
