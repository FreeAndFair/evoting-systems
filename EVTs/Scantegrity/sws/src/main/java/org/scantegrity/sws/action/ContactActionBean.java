/*
 * @(#)ContactActionBean.java
 *  
 * Copyright (C) 2008-2009 Scantegrity Project
 * 
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */

/**
 * Handles the contact form data and sends an e-mail.
 * 
 * @author Richard Carback
 */

package org.scantegrity.sws.action;

import java.util.Properties;
import java.util.ResourceBundle;

import javax.mail.Message;
import javax.mail.Session;
import javax.mail.Transport;
import javax.mail.internet.InternetAddress;
import javax.mail.internet.MimeMessage;
import javax.servlet.http.HttpServletRequest;

import net.sourceforge.stripes.action.DefaultHandler;
import net.sourceforge.stripes.action.ForwardResolution;
import net.sourceforge.stripes.action.Resolution;
import net.sourceforge.stripes.validation.SimpleError;
import net.sourceforge.stripes.validation.Validate;
import net.tanesha.recaptcha.ReCaptchaImpl;
import net.tanesha.recaptcha.ReCaptchaResponse;


public class ContactActionBean extends DefaultActionBean{
	private static final String FORM = "/WEB-INF/pages/contact.jsp";
	private static final String SUCCESS = "/WEB-INF/pages/contact-success.jsp";
	
	@Validate(required=true, minvalue=1)
	private String c_name;
	@Validate(required=false)
	private String c_email;
	@Validate(required=false)
	private String c_subject;
	@Validate(required=true, minvalue=5)
	private String c_msg;
	
	
	@Validate(required=false)
	private String c_captchaHTML;
	private ReCaptchaImpl c_ReCaptcha;
	ResourceBundle c_bundle;

	protected void initialize()
	{
		c_ReCaptcha = new ReCaptchaImpl();
		c_bundle = ResourceBundle.getBundle("Contact");
		c_ReCaptcha.setPrivateKey(c_bundle.getString("ReCaptchaPriv"));
		c_ReCaptcha.setPublicKey(c_bundle.getString("ReCaptchaPub"));
		c_ReCaptcha.setRecaptchaServer(ReCaptchaImpl.HTTPS_SERVER);
		c_ReCaptcha.setIncludeNoscript(true);
		System.out.println("Initialized");
	}
	
	@DefaultHandler
	public Resolution form()
	{
		System.out.println("DefaultHandler");
		c_captchaHTML = c_ReCaptcha.createRecaptchaHtml(null, null);
		return new ForwardResolution(FORM);
	}
	
	
	public Resolution submit()
	{
		/** TODO: This could be cleaned up a bit... **/
		
		Properties l_props;
		Session l_s;
		MimeMessage l_message;
		InternetAddress l_f, l_t;
		String l_subject, l_name, l_from, l_msg;
		HttpServletRequest l_req = getContext().getRequest();
		ReCaptchaResponse l_resp;
		
		try {
			l_resp = c_ReCaptcha.checkAnswer(l_req.getRemoteAddr(),
					l_req.getParameter("recaptcha_challenge_field"), 
					l_req.getParameter("recaptcha_response_field"));
			if (l_resp.isValid())
			{
				l_props = new Properties();
			  	l_props.setProperty("mail.smtp.host", c_bundle.getString("mail.smtp.host"));
			  	
			  	l_subject = getSubject();
			  	if (l_subject == null || l_subject.isEmpty())
			  		l_subject = "No Subject";
			  	l_subject = c_bundle.getString("subjectPrefix") + l_subject;
			  	
			  	l_from = getEmail();
			  	if (l_from == null || l_from.isEmpty()) l_from = "No E-mail";
			  	
			  	l_name = getName();
			  	if (l_name == null || l_name.isEmpty()) l_name = "No Name"; 
			  	
			  	l_msg = getMsg();
			  	if (l_msg == null || l_msg.isEmpty())
			  	{
			  		SimpleError l_e = new SimpleError("You must include a message.");
			  		getContext().getValidationErrors().add("No Message", l_e);
			  		return form();
			  	}
			  
			  	l_s = Session.getInstance(l_props, null);
			  	l_message = new MimeMessage(l_s);
			  	l_f = new InternetAddress(c_bundle.getString("FROM")); 
				l_message.setFrom(l_f);
				
				String l_to[] = c_bundle.getString("TO").split(",");
				for (String l_addr : l_to)
				{
					l_t = new InternetAddress(l_addr);
					l_message.addRecipient(Message.RecipientType.TO, l_t);				
				}
				l_message.setSubject(l_subject);
	
				l_msg = "Message From: " + l_name + ", " + l_from + "\n\n" + l_msg;
				l_message.setText(l_msg);
				
				Transport.send(l_message);
				
				return new ForwardResolution(SUCCESS);				
			}
			else
			{
				SimpleError l_e = new SimpleError("ReCaptcha Failed. "
						+ "Your answer was incorrect, please try again.");
				
				getContext().getValidationErrors().add("ReCaptcha", l_e);
			}
		} catch (Exception e) {
			e.printStackTrace();
			SimpleError l_e = new SimpleError("Error: {0}", e.toString());
			
			getContext().getValidationErrors().add("Exception", l_e);
		}

		return form();
	}


	/**
	 * @return the name
	 */
	public String getName() {
		return c_name;
	}


	/**
	 * @param p_name the name to set
	 */
	public void setName(String p_name) {
		c_name = p_name;
	}


	/**
	 * @return the email
	 */
	public String getEmail() {
		return c_email;
	}


	/**
	 * @param p_email the email to set
	 */
	public void setEmail(String p_email) {
		c_email = p_email;
	}


	/**
	 * @return the subject
	 */
	public String getSubject() {
		return c_subject;
	}


	/**
	 * @param p_subject the subject to set
	 */
	public void setSubject(String p_subject) {
		c_subject = p_subject;
	}


	/**
	 * @return the msg
	 */
	public String getMsg() {
		return c_msg;
	}


	/**
	 * @param p_msg the msg to set
	 */
	public void setMsg(String p_msg) {
		c_msg = p_msg;
	}


	/**
	 * @return the captchaHTML
	 */
	public String getCaptchaHTML() {
		return c_captchaHTML;
	}


	/**
	 * @param p_captchaHTML the captchaHTML to set
	 */
	public void setCaptchaHTML(String p_captchaHTML) {
		c_captchaHTML = p_captchaHTML;
	}
	

	
}