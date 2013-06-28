/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.scheduler.beans.JobTarget.java
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
  *  0.1		15-04-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.scheduler.beans;
import java.math.BigDecimal;
import java.rmi.RemoteException;

import com.logica.eplatform.error.EPlatformException;
/**
 * Remote interface for Enterprise Bean: JobTarget
 */
public interface JobTarget extends javax.ejb.EJBObject
{
	public void performExecute(BigDecimal jobID)
		throws EPlatformException, RemoteException;
}