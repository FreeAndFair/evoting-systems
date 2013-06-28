<%@ taglib uri="/WEB-INF/struts-bean.tld" prefix="bean" %>
<%@ taglib uri="/WEB-INF/struts-html.tld" prefix="html" %>
<%@ taglib uri="/WEB-INF/struts-logic.tld" prefix="logic" %>
<%@ taglib uri="/WEB-INF/struts-tiles.tld" prefix="tiles" %>
<%@ page import="org.apache.struts.action.ActionMessages" %>
<% 
  String contextPath = request.getContextPath();
  String username = (String)session.getAttribute("userID"); 
%>
<style>
	a, A:link, a:visited, a:active
		{color: #0000aa; text-decoration: none; font-family: Tahoma, Verdana; font-size: 11px;}
	A:hover
		{color: #ff0000; text-decoration: none; font-family: Tahoma, Verdana; font-size: 11px;}
	p, tr, td, ul, li
		{color: #000000; font-family: Tahoma, Verdana; font-size: 11px;}
	.header1, h1
		{color: #ffffff; background: #4682B4; font-weight: bold; font-family: Tahoma, Verdana; font-size: 13px; margin: 0px; padding: 2px;}
	.header2, h2
		{color: #000000; background: #DBEAF5; font-weight: bold; font-family: Tahoma, Verdana; font-size: 12px;}
	.intd
		{color: #000000; font-family: Tahoma, Verdana; font-size: 11px; padding-left: 15px;}

</style>
<link rel="stylesheet" href="<%=contextPath%>/web/menu/menu.css">
</head>

<body bottommargin="15" topmargin="15" leftmargin="15" rightmargin="15" marginheight="15" marginwidth="15" bgcolor="white">


<!-- menu script itself. you should not modify this file -->
<script language="JavaScript" src="<%=contextPath%>/web/menu/menu.js"></script>
<!-- items structure. menu hierarchy and links are stored there -->
<% if(username.equals("counting")) { %>
<script language="JavaScript" src="<%=contextPath%>/web/menu/counting_menu_items.js"></script>
<%} else {%>
<script language="JavaScript" src="<%=contextPath%>/web/menu/menu_items.js"></script>
<%}%>
<!-- files with geometry and styles structures -->
<script language="JavaScript" src="<%=contextPath%>/web/menu/menu_tpl.js"></script>
<script language="JavaScript">
	new epbMenu (MENU_ITEMS, MENU_POS);
</script>
</body>
