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
package com.logicacmg.koa.constants;
/**
 * The constant values representing the different
 * types of components available in the KOA system.
 * 
 * @author KuijerM
 * 
 */
public class ComponentType
{
	/**
	 * Private constructor to prevent 
	 * creating an instance of this class
	 * 
	 */
	private ComponentType()
	{
	}
	/**
	 * The constant value of the 
	 * 'Web Stem Machine' (WSM) component.
	 * 
	 */
	public final static String WEB = "WEB";
	/**
	 * The constant value of the 
	 * 'Telefonische Stem Machine' (TSM) component.
	 * 
	 */
	public final static String TEL = "TEL";
	/**
	 * The constant value of the 
	 * 'Stemproces' component.
	 * 
	 */
	public final static String STEM = "STEM";
	/**
	 * The constant value of the 
	 * 'Electonische Stembus' component.
	 * 
	 */
	public final static String ESB = "ESB";
	/**
	 * The constant value of the 
	 * 'KiezerRegistratie' component.
	 * 
	 */
	public final static String KR = "KR";
	/**
	 * Get the component type as an int
	 * 
	 * @param type Component type as string
	 * 
	 * @return Component type as int
	 */
	public static int getModaliteitAsInt(String type)
	{
		int retval = -1;
		if (type.equals(WEB))
		{
			retval = 0;
		}
		else if (type.equals(TEL))
		{
			retval = 1;
		}
		return retval;
	}
	/**
	 * Translates the technical name of a component to a nice dutch equivalent
	 * 
	 * @param sComponent - Name of the component to be translated
	 * @return If componentname has been recognized, the dutch equivalent else an empty string
	 */
	public static String translateComponentNameToDutch(String sComponentName)
	{
		if (sComponentName == null)
		{
			return "";
		}
		if (sComponentName.equals(WEB))
		{
			return "Stemmen per PC";
		}
		if (sComponentName.equals(TEL))
		{
			return "Stemmen per telefoon";
		}
		if (sComponentName.equals(KR))
		{
			return "Kiesregister";
		}
		if (sComponentName.equals(ESB))
		{
			return "Stembus";
		}
		return "";
	}
}
