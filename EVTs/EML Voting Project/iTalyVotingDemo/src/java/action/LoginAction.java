package action;

import dao.LoginDAO;
import forms.LoginForm;
import java.io.PrintStream;
import javax.servlet.http.*;
import org.apache.struts.action.*;
import util.MessageBean;

public class LoginAction extends Action
{

    public LoginAction()
    {
    }

    public ActionForward execute(ActionMapping actionmapping, ActionForm actionform, HttpServletRequest httpservletrequest, HttpServletResponse httpservletresponse)
        throws Exception
    {
        LoginForm loginform = (LoginForm)actionform;
        String s = "loginpage";
        boolean flag = false;
        String s1 = loginform.getUserID();
        String s2 = loginform.getPassword();
        MessageBean messagebean = new MessageBean();
        httpservletrequest.setAttribute("messageBean", messagebean);
        if(httpservletrequest.getParameter("pageAction") != null && httpservletrequest.getParameter("pageAction").endsWith("homePage"))
        {
            s = "loginpage";
            loginform.reset(actionmapping, httpservletrequest);
        } else
        if(httpservletrequest.getParameter("pageAction") != null && httpservletrequest.getParameter("pageAction").endsWith("logout"))
        {
            s = "logoutpage";
            loginform.reset(actionmapping, httpservletrequest);
            httpservletrequest.getSession().removeAttribute("userID");
            loginform.reset(actionmapping, httpservletrequest);
        } else
        if(isMissing(s1))
        {
            makeWarning(httpservletrequest, "Missing - User Name");
            s = "loginpage";
        } else
        if(isMissing(s2))
        {
            makeWarning(httpservletrequest, "Missing - Password");
            s = "loginpage";
        } else
        {
            LoginDAO logindao = new LoginDAO();
            boolean flag1 = logindao.loginDAO(loginform.getUserID(), loginform.getPassword());
            if(flag1)
            {
                HttpSession httpsession = httpservletrequest.getSession();
                httpsession.setAttribute("userID", s1);
                if(loginform.getUserID().equalsIgnoreCase("counting"))
                {
                    makeWarning(httpservletrequest, "Welcome to Counting! Please click on the given below enabled button to process the counting...! ");
                    s = "countingpage";
                } else
                {
                    s = "success";
                }
                httpservletrequest.getSession().setAttribute("login", loginform);
            } else
            {
                makeWarning(httpservletrequest, "Invalid User/Password");
                s = "loginpage";
            }
        }
        System.out.print("forwardStatus " + s);
        return actionmapping.findForward(s);
    }

    private boolean isMissing(String s)
    {
        return s == null || s.trim().equals("");
    }

    protected void makeWarning(HttpServletRequest httpservletrequest, String s)
    {
        MessageBean messagebean = (MessageBean)httpservletrequest.getAttribute("messageBean");
        messagebean.setMessage(s);
    }
}