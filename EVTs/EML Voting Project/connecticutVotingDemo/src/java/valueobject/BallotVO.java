package valueobject;

import java.util.HashMap;
import org.apache.struts.action.ActionForm;

public final class BallotVO extends ActionForm
{

    public BallotVO()
    {
        transactionDetails = null;
        ballotTransactionID = null;
        contextPath = null;
        hostName = null;
        ballotData = null;
        ballotLookupData = null;
        emlXMLData = null;
    }

    public String getBallotTransactionID()
    {
        return ballotTransactionID;
    }

    public void setBallotTransactionID(String s)
    {
        ballotTransactionID = s;
    }

    public HashMap getBallotData()
    {
        return ballotData;
    }

    public void setBallotData(HashMap hashmap)
    {
        ballotData = hashmap;
    }

    public HashMap getBallotLookupData()
    {
        return ballotLookupData;
    }

    public void setBallotLookupData(HashMap hashmap)
    {
        ballotLookupData = hashmap;
    }

    public HashMap getEmlXMLData()
    {
        return emlXMLData;
    }

    public void setEmlXMLData(HashMap hashmap)
    {
        emlXMLData = hashmap;
    }

    public String getTransactionDetails()
    {
        return transactionDetails;
    }

    public void setTransactionDetails(String s)
    {
        transactionDetails = s;
    }

    public String getHostName()
    {
        return hostName;
    }

    public void setHostName(String s)
    {
        hostName = s;
    }

    public String getContextPath()
    {
        return contextPath;
    }

    public void setContextPath(String s)
    {
        contextPath = s;
    }

    private String transactionDetails;
    private String ballotTransactionID;
    private String contextPath;
    private String hostName;
    private HashMap ballotData;
    private HashMap ballotLookupData;
    private HashMap emlXMLData;
}