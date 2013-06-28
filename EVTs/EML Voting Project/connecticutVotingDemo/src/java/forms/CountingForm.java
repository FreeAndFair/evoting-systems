package forms;

import org.apache.struts.action.ActionForm;

public final class CountingForm extends ActionForm
{

    public CountingForm()
    {
        countingType = null;
    }

    public String getCountingType()
    {
        return countingType;
    }

    public void setCountingType(String s)
    {
        countingType = s;
    }

    private String countingType;
}