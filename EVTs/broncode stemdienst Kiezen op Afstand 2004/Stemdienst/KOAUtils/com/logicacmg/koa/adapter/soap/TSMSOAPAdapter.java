/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.constants.ComponentType.java
  *
  * -----------------------------------------------------------------------
  * 
  *  (c) 2003  Ministerie van Binnenlandse Zaken en Koninkrijkrelaties
  *
  *  Project		: Kiezen Op Afstand (KOA)
  *  Project Number	: ECF-2651
  *  
  *  History:
  *  Version	Date		Name		Reason
  * ---------------------------------------------------------
  *  0.1		11-04-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.adapter.soap;
import org.apache.xml.utils.QName;

import sun.misc.Service;

import com.logicacmg.koa.adapter.soap.TSMSerializerFactories;
import com.logicacmg.koa.constants.ComponentType;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.SOAPInterfaceProperties;
import com.logicacmg.koa.constants.SystemState;
import com.logicacmg.koa.dataobjects.CounterData;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.soap.response.BlockResponse;
import com.logicacmg.koa.soap.response.CloseResponse;
import com.logicacmg.koa.soap.response.Counter;
import com.logicacmg.koa.soap.response.OpenResponse;
import com.logicacmg.koa.soap.response.PrepareForOpeningResponse;
import com.logicacmg.koa.soap.response.PrepareForReOpeningResponse;
import com.logicacmg.koa.soap.response.Statistics;
import com.logicacmg.koa.soap.response.SuspendResponse;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * The adapter to make sure communication is
 * possible between the TSM and the control client.
 * 
 * @author KuijerM
 */
public class TSMSOAPAdapter
{
	private String g_sIPAddress = null;
	private String g_sIdentifier = null;
	private String g_sControlclientID = null;
	private Statistics g_LatestStats = null;
	private TSMSerializerFactories g_sFactories = null;
	private String g_sEndpoint = null;
	private static int electionMode = 0;
	/**
	 * Constructor for the TSM SOAP adapter
	 * 
	 * @param sControlclientID The unique ID for the control client
	 * @param sIPAddress The IP address of the TSM
	 * @param sIdentifier The id
	 */
	public TSMSOAPAdapter(
		String sControlclientID,
		String sIPAddress,
		String sIdentifier)
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[TSMSOAPAdapter.constructor] Instantiating new TSMSoapAdapter for TSM: "
				+ g_sControlclientID);
		g_sFactories = TSMSerializerFactories.getInstance();
		g_sIPAddress = sIPAddress;
		g_sIdentifier = sIdentifier;
		g_sControlclientID = sControlclientID;
		try
		{
			g_sEndpoint =
				"http://"
					+ sIPAddress
					+ ":"
					+ SOAPInterfaceProperties.getProperty(
						SOAPInterfaceProperties.TSM_PORT)
					+ SOAPInterfaceProperties.getProperty(
						SOAPInterfaceProperties.TSM_URL);
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[TSMSOAPAdapter.constructor] TSM Endpoint: " + g_sEndpoint);
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"TSMSoapAdapter.constructor",
				"Cannot obtain TSM properties",
				koae);
		}
	}
	/**
	 * Notify the change of state at the moment the
	 * state changes.
	 * 
	 * @param sNewState the new state
	 */
	public boolean notifyState(String sNewState)
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[TSMSOAPAdapter.notifyState] got notified for new state "
				+ sNewState);
		boolean bSuccess = false;
		try
		{
			/* Walk through all available states and perform the associated action */
			if (sNewState.equals(SystemState.PREPARE))
			{
				// no explicit action from TSM required
			}
			else if (sNewState.equals(SystemState.INITIALIZED))
			{
				g_LatestStats = prepareForOpening(electionMode);
			}
			else if (sNewState.equals(SystemState.OPEN))
			{
				g_LatestStats = open();
			}
			else if (sNewState.equals(SystemState.BLOCKED))
			{
				g_LatestStats = block();
			}
			else if (sNewState.equals(SystemState.CLOSED))
			{
				g_LatestStats = close();
			}
			else if (sNewState.equals(SystemState.RE_INITIALIZED))
			{
				g_LatestStats = prepareForReOpening();
			}
			else if (sNewState.equals(SystemState.SUSPENDED))
			{
				g_LatestStats = suspend();
			}
			else if (sNewState.equals(SystemState.READY_TO_COUNT))
			{
				g_LatestStats = getStatistics();
				if (g_LatestStats == null)
				{
					return false;
				}
			}
			else if (sNewState.equals(SystemState.VOTES_COUNTED))
			{
				g_LatestStats = getStatistics();
				if (g_LatestStats == null)
				{
					return false;
				}
			}
			/* set the result to true */
			bSuccess = true;
		}
		catch (Exception e)
		{
			String[] params =
				{
					"Could not notify TSM component about new state "
						+ sNewState };
			KOALogHelper.logErrorCode(
				"TSMSOAPAdapter.notifyState",
				ErrorConstants.ERR_COMM_VSL_TO_TSM,
				params,
				e);
			bSuccess = false;
		}
		return bSuccess;
	}
	/**
	 * Collect the counters from the TSM
	 * and return a counterData object with this
	 * counter information.
	 * 
	 * @return CounterData object with all the counter information.
	 */
	public CounterData collectCounterData()
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[TSMSOAPAdapter.collectCounterData] controller requests counters for TSM: "
				+ g_sControlclientID);
		/* Counters are String, long couples */
		return StatsToCounterData(getStatistics(), g_sControlclientID);
	}
	private static CounterData StatsToCounterData(
		Statistics statistics,
		String controlclientID)
	{
		CounterData cData = new CounterData(ComponentType.TEL, controlclientID);
		Statistics stats = statistics;
		try
		{
			if (stats != null)
			{
				Counter[] counters = stats.getCounters();
				Counter counter;
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[TSMSOAPAdapter.collectCounterData] Looping through retrieved counters");
				for (int i = 0; i < counters.length; i++)
				{
					KOALogHelper.log(
						KOALogHelper.TRACE,
						"[TSMSOAPAdapter.collectCounterData] counter: " + i);
					counter = counters[i];
					if (counter != null)
					{
						KOALogHelper.log(
							KOALogHelper.TRACE,
							"[TSMSOAPAdapter.collectCounterData] counter: "
								+ i
								+ " KEY: "
								+ counter.getKey()
								+ " VALUE:"
								+ counter.getValue());
						/* Do a mapping to application known counters (see soapinterface.properties) */
						if (SOAPInterfaceProperties
							.getNullableProperty(counter.getKey())
							!= null)
						{
							/* A mapping is defined */
							cData.setCounter(
								SOAPInterfaceProperties.getNullableProperty(
									counter.getKey()),
								Long.parseLong(counter.getValue()));
						}
						else
						{
							/* No mapping found, use key provided by TSM */
							KOALogHelper.log(
								KOALogHelper.TRACE,
								"[TSMSOAPAdapter.collectCounterData] No definition found for key: "
									+ counter.getKey()
									+ ". Dropping counter!");
						}
					}
					else
					{
						KOALogHelper.log(
							KOALogHelper.TRACE,
							"[TSMSOAPAdapter.collectCounterData] counter: "
								+ i
								+ " appears to be null.");
					}
				}
			}
			else
			{
				KOALogHelper.logError(
					"TSMSoapAdapter.collectCounterData",
					"Collected statistics are null for TSM: " + controlclientID,
					null);
				return null;
			}
		}
		catch (Exception e)
		{
			String[] params =
				{
					"Error parsing collected statistics for TSM: "
						+ controlclientID };
			KOALogHelper.logErrorCode(
				"TSMSoapAdapter.collectCounterData",
				ErrorConstants.ERR_COMM_VSL_TO_TSM,
				params,
				e);
		}
		return cData;
	}
	/**
	 * Get a SOAP Call object for the given endpoint
	 * 
	 * @param endpoint
	 * @return Call Axis call object
	 */
	private Call getCall() throws Exception
	{
		Call call = null;
		try
		{
			// create call
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[TSMSOAPAdapter.getCall] New service");
			Service service = new Service();
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[TSMSOAPAdapter.getCall] Create call");
			call = (Call) service.createCall();
			/* Set configurable timeout on the connection */
			call.setTimeout(
				new Integer(
					SOAPInterfaceProperties.getProperty(
						SOAPInterfaceProperties.TSM_TIMEOUT)));
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[TSMSOAPAdapter.getCall] Register beanmappings");
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[TSMSOAPAdapter.getCall] Done setting mappings");
			// set operation style
			call.setOperationStyle("rpc");
			// set endpoint address
			call.setTargetEndpointAddress(new java.net.URL(g_sEndpoint));
			// set encoding style
			call.setEncodingStyle(org.apache.axis.Constants.URI_SOAP11_ENC);
		}
		catch (javax.xml.rpc.ServiceException se)
		{
			String[] params =
				{ "Service exception for TSM: " + g_sControlclientID };
			KOALogHelper.logErrorCode(
				"TSMSoapAdapter.getCall",
				ErrorConstants.ERR_COMM_VSL_TO_TSM,
				params,
				se);
			throw se;
		}
		catch (java.net.MalformedURLException mue)
		{
			String[] params =
				{ "Malformed URL Exception for TSM: " + g_sControlclientID };
			KOALogHelper.logErrorCode(
				"TSMSoapAdapter.getCall",
				ErrorConstants.ERR_COMM_VSL_TO_TSM,
				params,
				mue);
			throw mue;
		}
		return call;
	}
	/**
	 * Send a prepare for opening to the TSM
	 * 
	 * @param electionmode mode for the election (not used!)
	 */
	private Statistics prepareForOpening(int electionmode) throws Exception
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[TSMSOAPAdapter.prepareForOpening] TSM: " + g_sControlclientID);
		Call call = getCall();
		// Prepare for opening response
		call.registerTypeMapping(
			PrepareForOpeningResponse.class,
			g_sFactories.getPrepareForOpeningResponse(),
			g_sFactories.getSerPrepareForOpening(),
			g_sFactories.getDeserPrepareForOpening());
		call.setSOAPActionURI(
			"http://kiezenopafstand.nl/TSM/prepareForOpening");
		call.setOperationName(
			new QName("http://kiezenopafstand.nl/TSM", "prepareForOpening"));
		call.addParameter(
			new javax.xml.namespace.QName("", "electionmode"),
			new javax.xml.namespace.QName(
				"http://www.w3.org/2001/XMLSchema",
				"int"),
			java.lang.Integer.class,
			javax.xml.rpc.ParameterMode.IN);
		call.setReturnType(g_sFactories.getPrepareForOpeningResponse());
		try
		{
			PrepareForOpeningResponse ret =
				(PrepareForOpeningResponse) call.invoke(
					new Object[] { new Integer(electionmode)});
			if (ret.getReturncode() == -1)
			{
				KOALogHelper.logError(
					"TSMSoapAdapter.prepareForOpening",
					"TSM Returned an error for TSM: "
						+ g_sControlclientID
						+ ret.getErrormessage(),
					null);
			}
			return getStatistics();
		}
		catch (java.rmi.RemoteException re)
		{
			String[] params = { "TSM " + g_sControlclientID };
			KOALogHelper.logErrorCode(
				"TSMSoapAdapter.prepareForOpening",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw re;
		}
	}
	/**
	 * Send a prepare for reOpening to the TSM 
	 */
	private Statistics prepareForReOpening() throws Exception
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[TSMSOAPAdapter.prepareForReOpening] TSM: " + g_sControlclientID);
		Call call = getCall();
		// Prepare for reopening reponse
		call.registerTypeMapping(
			PrepareForReOpeningResponse.class,
			g_sFactories.getPrepareForReOpeningResponse(),
			g_sFactories.getSerPrepareForReOpening(),
			g_sFactories.getDeserPrepareForReOpening());
		call.setSOAPActionURI(
			"http://kiezenopafstand.nl/TSM/prepareForReOpening");
		call.setOperationName(
			new QName("http://kiezenopafstand.nl/TSM", "prepareForReOpening"));
		call.setReturnType(g_sFactories.getPrepareForReOpeningResponse());
		try
		{
			PrepareForReOpeningResponse ret =
				(PrepareForReOpeningResponse) call.invoke(new Object[] {
			});
			if (ret.getReturncode() == -1)
			{
				KOALogHelper.logError(
					"TSMSoapAdapter.prepareForReOpening",
					"TSM Returned an error for TSM: "
						+ g_sControlclientID
						+ ret.getErrormessage(),
					null);
			}
			return getStatistics();
		}
		catch (java.rmi.RemoteException re)
		{
			String[] params = { "TSM " + g_sControlclientID };
			KOALogHelper.logErrorCode(
				"TSMSoapAdapter.prepareForReOpening",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw re;
		}
	}
	/**
	 * Send a open to the TSM
	 */
	private Statistics open() throws Exception
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[TSMSOAPAdapter.open] TSM: " + g_sControlclientID);
		Call call = getCall();
		// Open response
		call.registerTypeMapping(
			OpenResponse.class,
			g_sFactories.getOpenResponse(),
			g_sFactories.getSerOpen(),
			g_sFactories.getDeserOpen());
		// Counter
		call.registerTypeMapping(
			Counter.class,
			g_sFactories.getCounter(),
			g_sFactories.getSerCounter(),
			g_sFactories.getDeserCounter());
		// Statistics
		call.registerTypeMapping(
			Statistics.class,
			g_sFactories.getStatistics(),
			g_sFactories.getSerStatistics(),
			g_sFactories.getDeserStatistics());
		call.setSOAPActionURI("http://kiezenopafstand.nl/TSM/open");
		call.setOperationName(
			new QName("http://kiezenopafstand.nl/TSM", "open"));
		call.setReturnType(g_sFactories.getOpenResponse());
		try
		{
			OpenResponse ret = (OpenResponse) call.invoke(new Object[] {
			});
			if (ret.getReturncode() == -1)
			{
				KOALogHelper.logError(
					"TSMSoapAdapter.open",
					"TSM Returned an error for TSM: "
						+ g_sControlclientID
						+ ret.getErrormessage(),
					null);
			}
			return ret.getStatistics();
		}
		catch (java.rmi.RemoteException re)
		{
			String[] params = { "TSM " + g_sControlclientID };
			KOALogHelper.logErrorCode(
				"TSMSoapAdapter.open",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw re;
		}
	}
	/**
	 * Send a suspend to the TSM
	 */
	private Statistics suspend() throws Exception
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[TSMSOAPAdapter.suspend] TSM: " + g_sControlclientID);
		Call call = getCall();
		// Suspend response
		call.registerTypeMapping(
			SuspendResponse.class,
			g_sFactories.getSuspendResponse(),
			g_sFactories.getSerSuspend(),
			g_sFactories.getDeserSuspend());
		// Counter
		call.registerTypeMapping(
			Counter.class,
			g_sFactories.getCounter(),
			g_sFactories.getSerCounter(),
			g_sFactories.getDeserCounter());
		// Statistics
		call.registerTypeMapping(
			Statistics.class,
			g_sFactories.getStatistics(),
			g_sFactories.getSerStatistics(),
			g_sFactories.getDeserStatistics());
		call.setSOAPActionURI("http://kiezenopafstand.nl/TSM/suspend");
		call.setOperationName(
			new QName("http://kiezenopafstand.nl/TSM", "suspend"));
		call.setReturnType(g_sFactories.getSuspendResponse());
		try
		{
			SuspendResponse ret = (SuspendResponse) call.invoke(new Object[] {
			});
			if (ret.getReturncode() == -1)
			{
				KOALogHelper.logError(
					"TSMSoapAdapter.suspend",
					"TSM Returned an error for TSM: "
						+ g_sControlclientID
						+ ret.getErrormessage(),
					null);
			}
			return ret.getStatistics();
		}
		catch (java.rmi.RemoteException re)
		{
			String[] params = { "TSM " + g_sControlclientID };
			KOALogHelper.logErrorCode(
				"TSMSoapAdapter.suspend",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw re;
		}
	}
	/**
	 * Send a block to the TSM
	 */
	private Statistics block() throws Exception
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[TSMSOAPAdapter.block] TSM: " + g_sControlclientID);
		Call call = getCall();
		// Block response
		call.registerTypeMapping(
			BlockResponse.class,
			g_sFactories.getBlockResponse(),
			g_sFactories.getSerBlock(),
			g_sFactories.getDeserBlock());
		// Counter
		call.registerTypeMapping(
			Counter.class,
			g_sFactories.getCounter(),
			g_sFactories.getSerCounter(),
			g_sFactories.getDeserCounter());
		// Statistics
		call.registerTypeMapping(
			Statistics.class,
			g_sFactories.getStatistics(),
			g_sFactories.getSerStatistics(),
			g_sFactories.getDeserStatistics());
		call.setSOAPActionURI("http://kiezenopafstand.nl/TSM/block");
		call.setOperationName(
			new QName("http://kiezenopafstand.nl/TSM", "block"));
		call.setReturnType(g_sFactories.getBlockResponse());
		try
		{
			BlockResponse ret = (BlockResponse) call.invoke(new Object[] {
			});
			if (ret.getReturncode() == -1)
			{
				KOALogHelper.logError(
					"TSMSoapAdapter.block",
					"TSM Returned an error for TSM: "
						+ g_sControlclientID
						+ ret.getErrormessage(),
					null);
			}
			return ret.getStatistics();
		}
		catch (java.rmi.RemoteException re)
		{
			String[] params = { "TSM " + g_sControlclientID };
			KOALogHelper.logErrorCode(
				"TSMSoapAdapter.block",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw re;
		}
	}
	/**
	 * send a close() to the TSM
	 */
	private Statistics close() throws Exception
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[TSMSOAPAdapter.close] TSM: " + g_sControlclientID);
		Call call = getCall();
		// close response
		call.registerTypeMapping(
			CloseResponse.class,
			g_sFactories.getCloseResponse(),
			g_sFactories.getSerClose(),
			g_sFactories.getDeserClose());
		// Counter
		call.registerTypeMapping(
			Counter.class,
			g_sFactories.getCounter(),
			g_sFactories.getSerCounter(),
			g_sFactories.getDeserCounter());
		// Statistics
		call.registerTypeMapping(
			Statistics.class,
			g_sFactories.getStatistics(),
			g_sFactories.getSerStatistics(),
			g_sFactories.getDeserStatistics());
		call.setSOAPActionURI("http://kiezenopafstand.nl/TSM/close");
		call.setOperationName(
			new QName("http://kiezenopafstand.nl/TSM", "close"));
		call.setReturnType(g_sFactories.getCloseResponse());
		try
		{
			CloseResponse ret = (CloseResponse) call.invoke(new Object[] {
			});
			if (ret.getReturncode() == -1)
			{
				KOALogHelper.logError(
					"TSMSoapAdapter.close",
					"TSM Returned an error for TSM: "
						+ g_sControlclientID
						+ ret.getErrormessage(),
					null);
			}
			return ret.getStatistics();
		}
		catch (java.rmi.RemoteException re)
		{
			String[] params = { "TSM " + g_sControlclientID };
			KOALogHelper.logErrorCode(
				"TSMSoapAdapter.close",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw re;
		}
	}
	/**
	 * get the statistics from the TSM
	 * 
	 * @return Statistics The collected statistics
	 */
	private Statistics getStatistics()
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[TSMSOAPAdapter.getStatistics] TSM: " + g_sControlclientID);
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[TSMSOAPAdapter.getStatistics] get Call");
		Call call = null;
		try
		{
			call = getCall();
		}
		catch (Exception ex)
		{
			KOALogHelper.logError(
				"TSMSOAPAdapter.getStatistics",
				"Could not get call for the SOAP service",
				ex);
			return null;
		}
		// Counter
		call.registerTypeMapping(
			Counter.class,
			g_sFactories.getCounter(),
			g_sFactories.getSerCounter(),
			g_sFactories.getDeserCounter());
		// Statistics
		call.registerTypeMapping(
			Statistics.class,
			g_sFactories.getStatistics(),
			g_sFactories.getSerStatistics(),
			g_sFactories.getDeserStatistics());
		Statistics ret = null;
		call.setSOAPActionURI("http://kiezenopafstand.nl/TSM/getStatistics");
		call.setOperationName(
			new QName("http://kiezenopafstand.nl/TSM", "getStatistics"));
		call.setReturnType(g_sFactories.getStatistics());
		try
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[TSMSOAPAdapter.getStatistics] Invoke");
			ret = (Statistics) call.invoke(new Object[] {
			});
		}
		catch (java.rmi.RemoteException re)
		{
			String[] params = { "TSM " + g_sControlclientID };
			KOALogHelper.logErrorCode(
				"TSMSoapAdapter.getStatistics",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
		}
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[TSMSOAPAdapter.getStatistics] Return");
		return ret;
	}
	/**
	 * Gets the LatestStats
	 * @return Returns the latest Statistics as received with the statechange
	 */
	public CounterData getLatestCounterData()
	{
		return StatsToCounterData(g_LatestStats, g_sControlclientID);
	}
}