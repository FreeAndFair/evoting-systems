/*
 * JML specification Copyright 2004 SoS Group, University of Nijmegen
 */

package sos.koa;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;

/**
 * The help window.
 *
 * @version $Id: HelpAdapter.java,v 1.23 2004/05/05 21:28:04 martijno Exp $
 *
 * @author Engelbert Hubbers (hubbers@cs.kun.nl)
 * Dehubbified by MO, meta-dehubbified and HTMLed by CB + MO.
 */
public class HelpAdapter extends JFrame implements ActionListener, KOAConstants { 

   /*@ spec_public */ static final Dimension PREFERRED_SIZE = new Dimension(500,500);

   static final String FUNCTIONS_STRING = "Op dit moment kunt u kiezen uit de volgende functies:";
   static final String INIT_STATE_STRING = "U bevindt zich in de begintoestand van dit programma; er is nog niets gedaan.";
   static final String CLEARED_STATE_STRING = "Alle oude gegevens zijn gewist en u bent klaar om de kandidatengegevens in te lezen.";
   static final String CANDIDATES_IMPORTED_STATE_STRING = "De kandidatengegevens zijn ingelezen.";
   static final String VOTES_IMPORTED_STATE_STRING = "De kandidatengegevens en het exportbestand van de stembus zijn ingelezen en u bent klaar om de sleutels in te lezen.";
   static final String PRIVATE_KEY_IMPORTED_STATE_STRING = "De kandidatengegevens, de stembusexport en een correcte private sleutel zijn ingelezen.";
   static final String PUBLIC_KEY_IMPORTED_STATE_STRING = "De kandidatengegevens, de stembusexport, een correcte private sleutel en een bijbehorende publieke sleutel zijn ingelezen.";
   static final String VOTES_DECRYPTED_STATE_STRING = "Alle gegevens zijn ingelezen en de versleutelde stemmen zijn ontsleuteld en kunnen nu geteld worden.";
   static final String VOTES_COUNTED_STATE_STRING = "Alle gegevens zijn ingelezen, de versleutelde stemmen zijn ontsleuteld en vervolgens geteld. U kunt nu de rapporten maken.";
   static final String REPORT_GENERATED_STATE_STRING = "Er is minimaal een rapport gemaakt.";

   static final String FUNCTION_CLEAR = "<b>" + CLEAR_BUT_TXT + "</b><br>"
      + "Deze functie wist het interne geheugen en eventuele bestanden op de harde schijf. Er wordt om een bevestiging gevraagd voordat er definitief gegevens verwijderd worden.";

   static final String FUNCTION_RESTART = "<b>" + RESTART_BUT_TXT + "</b><br>"
      + "Deze functie breekt een telsessie af en brengt het programma weer in de begintoestand. Er worden nog geen gegevens gewist.";

   static final String FUNCTION_IMPORT_CANDIDATES = "<b>" + IMPORT_CANDIDATES_BUT_TXT + "</b><br>"
      + "Deze functie probeert het bestand met de kandidaten en hun codes in te lezen. U geeft de plaats aan waar dit bestand staat. Als dit een geldig bestand is, wordt het resultaat weergegeven op het scherm en kunt u aangeven of u verder wil werken met deze gegevens of niet.";

   static final String FUNCTION_IMPORT_VOTES = "<b>" + IMPORT_VOTES_BUT_TXT + "</b><br>"
      + "Deze functie probeert het exportbestand van de stembus met de versleutelde stemmen te lezen. U geeft de plaats aan waar het bestand staat. Als dit een geldig bestand is, wordt het resultaat weergegeven op het scherm en kunt u aangeven of u verder wil werken met deze gegevens of niet.";

   static final String FUNCTION_IMPORT_PRIVATE_KEY = "<b>" + IMPORT_PRIVATE_KEY_BUT_TXT + "</b><br>"
      + "Deze functie probeert de private sleutel te lezen. U geeft eerst de plaats aan waar het bestand met deze sleutel staat. Vervolgens dient u het bijbehorende wachtwoord in te voeren.";

   static final String FUNCTION_IMPORT_PUBLIC_KEY = "<b>" + IMPORT_PUBLIC_KEY_BUT_TXT + "</b><br>"
      + "Deze functie probeert de publieke sleutel te lezen. U geeft eerst de plaats aan waar het bestand met de publieke sleutel staat. Vervolgens dient u het bijbehorende wachtwoord in te voeren. Als het wachtwoord klopt en het bestand bevat een geldige publieke sleutel,  wordt vervolgens getest of deze sleutel ook echt bij de al eerder ingelezen private sleutel hoort.";

   static final String FUNCTION_DECRYPT = "<b>" + DECRYPT_BUT_TXT + "</b><br>"
      + "Deze functie probeert alle ingelezen stemmen te ontsleutelen. Eventuele foutmeldingen worden per stem bijgehouden.";

   static final String FUNCTION_COUNT = "<b>" + COUNT_BUT_TXT + "</b><br>"
      + "Deze functie probeert alle ontsleutelde stemmen te tellen. Hierbij wordt tevens gecheckt of het een geldige stem is. Ongeldige stemmen worden uiteraard niet meegeteld.";

   static final String FUNCTION_REPORT = "<b>" + REPORT_BUT_TXT + "</b><br>"
      + "Deze functie vraagt u welk rapport u wilt hebben: het verwerkingsverslag of de uiteindelijke uitkomst van de stemming.De rapporten worden altijd op de harde schijf  opgeslagen.Het programma kijkt of er een PDF-viewer aanwezig is op uw systeem om het bestand meteen te bekijken. Als u een specifieke viewer wil gebruiken, kan dat door het programma met <code>java -DPdfViewer=my_viewer sos.koa.MenuPanel</code> op te starten.";

   static final String FUNCTION_EXIT = "<b>" + EXIT_BUT_TXT + "</b><br>"
      + "Hiermee stopt u het programma. Er worden geen bestanden weggeschreven, dus de huidige inhoud van het geheugen gaat verloren.";

   static final String FUNCTION_EXIT_REPORT = "De reeds op de harde schijf aangemaakte rapporten blijven bestaan.";

   /** The HTML text area of the help pane. */
   /*@ spec_public */ JEditorPane area;

   /**
    * Constructs the help window.
    */
   /*@ modifies this.area;
     @ ensures true;
    */
   public HelpAdapter() {
      super(HELP_TASK_MSG);
      area = new JEditorPane("text/html","");
      area.setEditable(false);
      Container contentPane = getContentPane();
      contentPane.add(new JScrollPane(area));
      pack();
   }

   /**
    * Gets executed when user presses the help button.
    *
    * @param ae an event indicating the user pressed the help button.
    */
   public void actionPerformed(ActionEvent ae) {
      setText(MenuPanel.getTheMenuPanel().getState());
      setVisible(!isVisible());
      setSize(PREFERRED_SIZE);
   }

   /**
    * Gets executed when user closes the help window.
    *
    * @param e event indicating the user closed the help window.
    */
   public void windowClosing(WindowEvent e) {
   }

   /**
    * Generates a text based on the current state and puts it in the help
    * window.
    *
    * @param state the current state.
    */
   /*@ requires INIT_STATE <= state &
     @          state <= REPORT_GENERATED_STATE;
     @ modifies \everything;
     @ ensures true;
    */
   public void setText(int state) {
      String txt = "<html>"
         + "<body>"
         + "<h1><font color=\"red\">" + stateString(state) + "</font></h1>"
         + "<h2>" + FUNCTIONS_STRING + "</h2>"
         + "<ul>";
      txt += "<li>" + FUNCTION_RESTART + "</li><br>";
      switch (state) {
         case INIT_STATE:
               txt += "<li>" + FUNCTION_CLEAR + "</li><br>"
                   + "<li>" + FUNCTION_EXIT + "</li><br>";
            break; 
         case CLEARED_STATE:
               txt += "<li>" + FUNCTION_IMPORT_CANDIDATES + "</li><br>"
                   + "<li>" + FUNCTION_EXIT + "</li><br>";
            break; 
         case CANDIDATES_IMPORTED_STATE:
               txt += "<li>" + FUNCTION_IMPORT_VOTES + "</li><br>"
                   + "<li>" + FUNCTION_EXIT + "</li><br>";
            break; 
         case VOTES_IMPORTED_STATE:
               txt += "<li>" + FUNCTION_IMPORT_PRIVATE_KEY + "</li><br>"
                   + "<li>" + FUNCTION_EXIT + "</li><br>";
            break; 
         case PRIVATE_KEY_IMPORTED_STATE:
               txt += "<li>" + FUNCTION_IMPORT_PUBLIC_KEY + "</li><br>"
                   + "<li>" + FUNCTION_EXIT + "</li><br>";
            break; 
         case PUBLIC_KEY_IMPORTED_STATE:
               txt += "<li>" + FUNCTION_DECRYPT + "</li><br>"
                   + "<li>" + FUNCTION_EXIT + "</li><br>";
            break; 
         case VOTES_DECRYPTED_STATE:
               txt += "<li>" + FUNCTION_COUNT + "</li><br>"
                   + "<li>" + FUNCTION_EXIT + "</li><br>";
            break; 
         case VOTES_COUNTED_STATE:
               txt += "<li>" + FUNCTION_REPORT + "</li><br>"
                   + "<li>" + FUNCTION_EXIT + "</li><br>";
            break; 
         case REPORT_GENERATED_STATE:
               txt += "<li>" + FUNCTION_REPORT + "</li><br>"
                   + "<li>" + FUNCTION_EXIT
                   + FUNCTION_EXIT_REPORT + "</li><br>";
            break; 
      }
      txt += "</ul>"
         + "</body></html>";
      setText(txt);
   }

   /**
    * Sets the text in the help window to <code>txt</code>.
    * The text can be a HTML document.
    *
    * @param txt the new text.
    */
   public void setText(String txt) {
      area.setText(txt);
   }

   /**
    * Gets a string that describes the current state.
    *
    * @param state the current state.
    */
   /*@ requires INIT_STATE <= state &
     @          state <= REPORT_GENERATED_STATE;
     @ ensures \result != null;
    */
   private /*@ pure */ String stateString(int state) {
      switch (state) {
         case INIT_STATE:
            return INIT_STATE_STRING;
         case CLEARED_STATE:
            return CLEARED_STATE_STRING;
         case CANDIDATES_IMPORTED_STATE:
            return CANDIDATES_IMPORTED_STATE_STRING;
         case VOTES_IMPORTED_STATE:
            return VOTES_IMPORTED_STATE_STRING;
         case PRIVATE_KEY_IMPORTED_STATE:
            return PRIVATE_KEY_IMPORTED_STATE_STRING;
         case PUBLIC_KEY_IMPORTED_STATE:
            return PUBLIC_KEY_IMPORTED_STATE_STRING;
         case VOTES_DECRYPTED_STATE:
            return VOTES_DECRYPTED_STATE_STRING;
         case VOTES_COUNTED_STATE:
            return VOTES_COUNTED_STATE_STRING;
         case REPORT_GENERATED_STATE:
            return REPORT_GENERATED_STATE_STRING;
      }
      return null;
   }

   /**
    * The preferred size of the help window.
    *
    * @return <code>PREFERRED_SIZE</code>.
    */
   /*@ also
     @ requires true;
     @ ensures \result == PREFERRED_SIZE;
    */
   public /*@ pure */ Dimension getPreferredSize() {
      return PREFERRED_SIZE;
   }
}

