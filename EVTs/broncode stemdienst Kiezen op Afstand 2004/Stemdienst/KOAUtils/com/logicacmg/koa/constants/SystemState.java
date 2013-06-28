/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.constants.SystemState.java
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
  *  0.1		11-04-2003	MKu		First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.constants;
import java.io.IOException;
import java.util.Vector;

import com.logica.eplatform.error.ErrorMessageFactory;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * All possible states the KOA system could
 * have are bundled in this class.
 * Every state has a constant value.
 * 
 * @author KuijerM
 * 
 */
public class SystemState
{
	/**
	 * Private constructor to prevent 
	 * creating an instance of this class
	 * 
	 */
	private SystemState()
	{
	}
	/**
	 * The system state is not known
	 * 
	 */
	public final static String UNKNOWN = "UNKNOWN";
	/**
	 * The system will be prepared for the elections
	 * 
	 */
	public final static String PREPARE = "PREPARE";
	/**
	 * The system is initialized and ready to be opened
	 * 
	 */
	public final static String INITIALIZED = "INITIALIZED";
	/**
	 * The system is open. In this state votes can be 
	 * posted to the system.
	 * 
	 */
	public final static String OPEN = "OPEN";
	/**
	 * The system is blocked. If the system indicates that 
	 * there are inconsistenties, it automatically will 
	 * block.
	 * 
	 */
	public final static String BLOCKED = "BLOCKED";
	/**
	 * The system is suspended. During elections and there 
	 * can not be voted.
	 * 
	 */
	public final static String SUSPENDED = "SUSPENDED";
	/**
	 * The system is closed. There can not be voted anymore.
	 * 
	 */
	public final static String CLOSED = "CLOSED";
	/**
	 * The system is re-initialized. It is ready to be
	 * opened.
	 * 
	 */
	public final static String RE_INITIALIZED = "RE_INITIALIZED";
	/**
	 * The system is closed and the system is ready to
	 * count the votes. 
	 * 
	 */
	public final static String READY_TO_COUNT = "READY_TO_COUNT";
	/**
	 * The system has counted the votes. This is the final 
	 * state.
	 * 
	 */
	public final static String VOTES_COUNTED = "VOTES_COUNTED";
	/**
	 * Get the system state mapped to an Integer
	 * 
	 */
	public static int getStateAsInt(String sState)
	{
		if (sState.equals(UNKNOWN))
			return -1;
		if (sState.equals(PREPARE))
			return 0;
		if (sState.equals(INITIALIZED))
			return 1;
		if (sState.equals(RE_INITIALIZED))
			return 2;
		if (sState.equals(OPEN))
			return 3;
		if (sState.equals(SUSPENDED))
			return 4;
		if (sState.equals(BLOCKED))
			return 5;
		if (sState.equals(READY_TO_COUNT)
			|| sState.equals(VOTES_COUNTED)
			|| sState.equals(CLOSED))
			return 6;
		return -1;
	}
	/**
	 * Method to determine if the system state should be altered 
	 * before actions are executed on the components, or after the 
	 * actions have been executed.
	 * 
	 * @param sCurrentState The current state
	 * @param sNewState the new state
	 * 
	 * @return boolean indicating if the state is changed before executing the components (true) or after executing the components (false) 
	 * 
	 */
	public static boolean changeSystemStateFirst(
		String sCurrentState,
		String sNewState)
	{
		/* if the new state is blocked always change the system state first */
		if (sNewState.equals(BLOCKED))
		{
			return true;
		}
		/* if the currentstate is prepare 
		and new state is initialized*/
		if (sCurrentState.equals(PREPARE) && sNewState.equals(INITIALIZED))
		{
			/* false means that the state is changed
			after all the components have executed changes */
			return false;
		}
		/* if the currentstate is initialized and new state
		is open*/
		else if (sCurrentState.equals(INITIALIZED) && sNewState.equals(OPEN))
		{
			/* false means that the state is changed
			after all the components have executed changes */
			return false;
		}
		/* if the currentstate is open and new state
		is closed */
		else if (sCurrentState.equals(OPEN) && sNewState.equals(CLOSED))
		{
			/* true means that the state is changed
			first, before all the components have executed changes */
			return true;
		}
		/* if the currentstate is open and new state
		is closed */
		else if (sCurrentState.equals(OPEN) && sNewState.equals(SUSPENDED))
		{
			/* true means that the state is changed
			first, before all the components have executed changes */
			return true;
		}
		/* if the currentstate is blocked and new state
		is suspended */
		else if (sCurrentState.equals(BLOCKED) && sNewState.equals(SUSPENDED))
		{
			/* false means that the state is changed
			after all the components have executed changes */
			return false;
		}
		/* if the currentstate is suspended and new state
		is closed */
		else if (sCurrentState.equals(SUSPENDED) && sNewState.equals(CLOSED))
		{
			/* true means that the state is changed
			first, before all the components have executed changes */
			return true;
		}
		/* if the currentstate is suspended and new state
		is re-initialized */
		else if (
			sCurrentState.equals(SUSPENDED)
				&& sNewState.equals(RE_INITIALIZED))
		{
			/* false means that the state is changed
			after all the components have executed changes */
			return false;
		}
		/* if the currentstate is re-initialized and new state
		is open */
		else if (
			sCurrentState.equals(RE_INITIALIZED) && sNewState.equals(OPEN))
		{
			/* false means that the state is changed
			after all the components have executed changes */
			return false;
		}
		/* if the currentstate is closed and new state
		is ready to count */
		else if (
			sCurrentState.equals(CLOSED) && sNewState.equals(READY_TO_COUNT))
		{
			/* false means that the state is changed
			after all the components have executed changes */
			return false;
		}
		/* if the currentstate is ready to count and new state
		is votes counted */
		else if (
			sCurrentState.equals(READY_TO_COUNT)
				&& sNewState.equals(VOTES_COUNTED))
		{
			/* false means that the state is changed
			after all the components have executed changes */
			return false;
		}
		/* false means that the state is changed
		after all the components have executed changes */
		return false;
	}
	/**
	 * Method to get all the available valid states to change
	 * to based on the current state.
	 * 
	 * @param sCurrentState The current state
	 * 
	 * @return Vector with all states (String) that are valid to change to
	 * 
	 */
	public static Vector getValidStateChanges(String sCurrentState)
	{
		Vector vValidStates = new Vector();
		/* if the currentstate is prepare */
		if (sCurrentState.equals(PREPARE))
		{
			vValidStates.add(INITIALIZED);
		}
		/* if the currentstate is initialized */
		else if (sCurrentState.equals(INITIALIZED))
		{
			vValidStates.add(OPEN);
		}
		/* if the currentstate is open */
		else if (sCurrentState.equals(OPEN))
		{
			vValidStates.add(CLOSED);
			vValidStates.add(BLOCKED);
			vValidStates.add(SUSPENDED);
		}
		/* if the currentstate is blocked */
		else if (sCurrentState.equals(BLOCKED))
		{
			vValidStates.add(SUSPENDED);
		}
		/* if the currentstate is suspended */
		else if (sCurrentState.equals(SUSPENDED))
		{
			vValidStates.add(CLOSED);
			vValidStates.add(RE_INITIALIZED);
		}
		/* if the currentstate is re-initialized */
		else if (sCurrentState.equals(RE_INITIALIZED))
		{
			vValidStates.add(OPEN);
			vValidStates.add(SUSPENDED);
		}
		/* if the currentstate is closed */
		else if (sCurrentState.equals(CLOSED))
		{
			vValidStates.add(READY_TO_COUNT);
		}
		/* if the currentstate is ready to count */
		else if (sCurrentState.equals(READY_TO_COUNT))
		{
			vValidStates.add(VOTES_COUNTED);
		}
		return vValidStates;
	}
	/**
	 * Translates the State key to a dutch discription of the state.
	 * 
	 * @param stateKey The key of the state to translate
	 * 
	 * @return String the translation of the state key
	 * 
	 */
	public static String getDutchTranslationForState(String stateKey)
	{
		if (stateKey == null)
		{
			return "Onbekende status";
		}
		stateKey = stateKey.trim();
		if (stateKey.equals(SystemState.PREPARE))
		{
			return "Voorbereiding";
		}
		else if (stateKey.equals(SystemState.INITIALIZED))
		{
			return "Gereed voor openen";
		}
		else if (stateKey.equals(SystemState.OPEN))
		{
			return "Open";
		}
		else if (stateKey.equals(SystemState.SUSPENDED))
		{
			return "Onderbroken";
		}
		else if (stateKey.equals(SystemState.RE_INITIALIZED))
		{
			return "Gereed voor hervatten";
		}
		else if (stateKey.equals(SystemState.BLOCKED))
		{
			return "Geblokkeerd";
		}
		else if (stateKey.equals(SystemState.CLOSED))
		{
			return "Gesloten";
		}
		else if (stateKey.equals(SystemState.READY_TO_COUNT))
		{
			return "Gereed voor stemopneming";
		}
		else if (stateKey.equals(SystemState.VOTES_COUNTED))
		{
			return "Stemopneming uitgevoerd";
		}
		else
		{
			return stateKey;
		}
	}
	/**
	 * Method to determine if the state change should only be 
	 * performed when all notification are succesful or always
	 * change the state.
	 * 
	 * @param sCurrentState The currentstate
	 * @param sNewState The new state
	 * 
	 * @return boolean The boolean indicating only to change state if succesfully notified all components (True) or always change state (false)
	 * 
	 */
	public static boolean changeStateOnlyForSuccesfulNotify(
		String sCurrentState,
		String sNewState)
	{
		/* check if the systemstate should be changed first,
		if this is true, always change state, because
		this means the state change is to important to cancel */
		if (changeSystemStateFirst(sCurrentState, sNewState))
		{
			/* false means always change state */
			return false;
		}
		/* if the currentstate is prepare 
		and new state is initialized*/
		if (sCurrentState.equals(PREPARE) && sNewState.equals(INITIALIZED))
		{
			/* true means only change state if notify succefully */
			return true;
		}
		/* if the currentstate is initialized and new state
		is open*/
		else if (sCurrentState.equals(INITIALIZED) && sNewState.equals(OPEN))
		{
			/* true means only change state if notify succefully */
			return true;
		}
		/* if the currentstate is open and new state
		is closed */
		else if (sCurrentState.equals(OPEN) && sNewState.equals(CLOSED))
		{
			/* false means always change state */
			return false;
		}
		/* if the currentstate is open and new state
		is blocked */
		else if (sCurrentState.equals(OPEN) && sNewState.equals(BLOCKED))
		{
			/* false means always change state */
			return false;
		}
		/* if the currentstate is open and new state
		is closed */
		else if (sCurrentState.equals(OPEN) && sNewState.equals(SUSPENDED))
		{
			/* false means always change state */
			return false;
		}
		/* if the currentstate is blocked and new state
		is suspended */
		else if (sCurrentState.equals(BLOCKED) && sNewState.equals(SUSPENDED))
		{
			/* false means always change state */
			return false;
		}
		/* if the currentstate is suspended and new state
		is closed */
		else if (sCurrentState.equals(SUSPENDED) && sNewState.equals(CLOSED))
		{
			/* false means always change state */
			return false;
		}
		/* if the currentstate is suspended and new state
		is re-initialized */
		else if (
			sCurrentState.equals(SUSPENDED)
				&& sNewState.equals(RE_INITIALIZED))
		{
			/* true means only change state if notify succefully */
			return true;
		}
		/* if the currentstate is re-initialized and new state
		is open */
		else if (
			sCurrentState.equals(RE_INITIALIZED) && sNewState.equals(OPEN))
		{
			/* true means only change state if notify succefully */
			return true;
		}
		/* if the currentstate is closed and new state
		is ready to count */
		else if (
			sCurrentState.equals(CLOSED) && sNewState.equals(READY_TO_COUNT))
		{
			/* false means always change state */
			return false;
		}
		/* if the currentstate is ready to count and new state
		is votes counted */
		else if (
			sCurrentState.equals(READY_TO_COUNT)
				&& sNewState.equals(VOTES_COUNTED))
		{
			/* false means always change state */
			return false;
		}
		/* false means always change state */
		return false;
	}
	/**
	 * Translates the State key to a whole text to show on the web page for
	 * the voter.
	 * 
	 * @param stateKey The key of the state to translate
	 * 
	 * @return String the text saying the elections are open or closed.
	 * 
	 */
	public static String getWebTextForState(String sCurrentState)
	{
		String sText = null;
		if (sCurrentState == null || sCurrentState.equals(SystemState.UNKNOWN))
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[SystemState.getWebTextForState] state unknown");
			return sText;
		}
		try
		{
			ErrorMessageFactory msgFactory =
				ErrorMessageFactory.getErrorMessageFactory();
			if (sCurrentState.equals(SystemState.OPEN))
			{
				sText = null;
			}
			else if (
				sCurrentState.equals(SystemState.PREPARE)
					|| sCurrentState.equals(SystemState.INITIALIZED))
			{
				sText =
					msgFactory.getErrorMessage(
						ErrorConstants.ERR_ELECTION_NOT_YET_OPEN,
						null);
			}
			else if (sCurrentState.equals(SystemState.BLOCKED))
			{
				sText =
					msgFactory.getErrorMessage(
						ErrorConstants.ERR_ELECTION_BLOCKED,
						null);
			}
			else if (
				sCurrentState.equals(SystemState.SUSPENDED)
					|| sCurrentState.equals(SystemState.RE_INITIALIZED))
			{
				sText =
					msgFactory.getErrorMessage(
						ErrorConstants.ERR_ELECTION_SUSPENDED,
						null);
			}
			else if (
				sCurrentState.equals(SystemState.CLOSED)
					|| sCurrentState.equals(SystemState.READY_TO_COUNT)
					|| sCurrentState.equals(SystemState.VOTES_COUNTED))
			{
				sText =
					msgFactory.getErrorMessage(
						ErrorConstants.ERR_ELECTION_CLOSED,
						null);
			}
		}
		catch (IOException ioe)
		{
			KOALogHelper.logError(
				"SystemState.getWebTextForState",
				"Failed to get status messages from ErrorMessageFactory",
				ioe);
		}
		return sText;
	}
}