package uk.ac.surrey.pav.administrator;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

public abstract class ButtonHandler implements ActionListener {
	VisualAdministrator adapter;

	public ButtonHandler(VisualAdministrator v) {
		this.adapter = v;
	}

	public abstract void actionPerformed(ActionEvent e);
}
