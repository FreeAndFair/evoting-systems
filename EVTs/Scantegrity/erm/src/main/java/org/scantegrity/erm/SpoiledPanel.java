package org.scantegrity.erm;

import java.awt.GridBagLayout;

import javax.swing.JPanel;

public class SpoiledPanel extends LoadPanel {

	private static final long serialVersionUID = 1L;
	WriteInResolver c_resolver = null;
	/**
	 * This is the default constructor
	 */
	public SpoiledPanel(WriteInResolver p_resolver, String p_destFolder) {
		super(p_resolver, null, p_destFolder);
		c_resolver = p_resolver;
	}

}
