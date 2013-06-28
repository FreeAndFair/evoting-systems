package forms;

import javax.servlet.http.HttpServletRequest;
import org.apache.struts.action.ActionForm;
import org.apache.struts.action.ActionMapping;

public final class LoginForm extends ActionForm
{

    public LoginForm()
    {
        userID = null;
        password = null;
    }

    public String getPassword()
    {
        return password;
    }

    public void setPassword(String s)
    {
        password = s;
    }

    public String getUserID()
    {
        return userID;
    }

    public void setUserID(String s)
    {
        userID = s;
    }

    public void reset(ActionMapping actionmapping, HttpServletRequest httpservletrequest)
    {
        userID = null;
        password = null;
    }

    private String userID;
    private String password;
}