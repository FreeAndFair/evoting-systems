package forms;

import javax.servlet.http.HttpServletRequest;
import org.apache.struts.action.ActionForm;
import org.apache.struts.action.ActionMapping;

public final class VoterForm extends ActionForm
{

    public VoterForm()
    {
        barCode = null;
    }

    public String getBarCode()
    {
        return barCode;
    }

    public void setBarCode(String s)
    {
        barCode = s;
    }

    public void reset(ActionMapping actionmapping, HttpServletRequest httpservletrequest)
    {
        barCode = null;
    }

    private String barCode;
}